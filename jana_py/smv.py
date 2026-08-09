"""Compile the scalar fragment of Janus to an nuXmv (SMV) model.

Janus guarantees reversibility *syntactically*, but the assertions it relies on
— the `fi` exit condition, the `from` entry condition, `delocal`, `assert`, and
the divisibility side conditions of `*=` and `/=` — can fail at run time.  A
program whose assertions never fail on a given domain is a **total** injection
on that domain; one whose assertions can fail is only a partial one.

This module turns "no assertion can fail" into a reachability question.  The
program becomes a transition system over a program counter and its integer
variables, every assertion becomes a branch into a distinguished error location,
and the property is `INVARSPEC pc != ERR`.  nuXmv's IC3 then either proves it
with an inductive invariant — over **unbounded** integers, which no amount of
testing can do — or returns a concrete counterexample store.

**Large-block encoding.**  A statement does *not* get its own program location.
Straight-line code is executed symbolically into a pending map (variable → an
expression over the values at the block's entry) plus a path condition, and a
location is cut only where control actually branches or merges.  So

    v += g   h -= v   h += halfg   t += 1

becomes one transition whose update for `h` is `((h - (v + g)) + halfg)`, not
four transitions.  Because expression translation *reads* the pending map, the
sequential composition happens as the expressions are built and no substitution
pass over already-generated text is ever needed.

Two output shapes are available.  `style="trans"` writes one big disjunction of
edges, each restating `next(v) = v` for every unchanged variable;
`style="assign"` writes one next-state function per variable, where a single
`TRUE` default absorbs all of those frame conditions.

Three traps this encoding has to avoid, all of which a naive translation falls
into and the first two of which would silently turn a proof into a lie:

* **Integer division.**  nuXmv's `/` truncates toward zero, while Janus (like
  Python) floors, and nuXmv's `mod` is not available on integers at all inside
  the SMT engine.  Every division site is therefore emitted through the
  floor-division macro `_div_defines` builds, checked against the interpreter's
  semantics in `tests/verify/test_smv.py`.
* **Aliasing is a run-time check, not a static one.**  `x += x` passes
  `validate_program` and is rejected only when PyJanus reaches it, so the
  obvious translation `next(x) = x + x` would model a non-injective program as
  a safe one.  After inlining resolves parameters the alias is syntactic, so
  reaching such a statement is itself the error.  The same holds for `x <=> x`,
  whose symbolic execution is the *identity*; and because the check is per
  statement, two formals resolving to one variable is not itself an error.
  `coq/RevSmvAlias.v` proves this decision exactly matches the reference
  semantics in both directions.
* **Sort confusion.**  Janus comparisons yield integers, so `x += (y > 0)` is
  legal.  The translation is two-sorted and *refuses* such expressions rather
  than guessing — the same discipline `coq/RevLowerExpr.v` formalizes as `wf`.

The same reasoning refuses the **modular modes**: `-m BITS` and `-p PRIME` wrap
every value, while this back-end emits unbounded integers, so a model built for
them would be about a different program.  `coq/RevSMod.v` and `RevExtSMod.v` are
the verified target for encoding them properly, and the obligations would have to
change with it — in a residue ring `*=` / `/=` need their factor to be a *unit*,
not merely nonzero.

Anything outside the fragment raises `SmvUnsupported`; nothing is ever emitted
as an approximation.
"""

from __future__ import annotations

from dataclasses import dataclass

from .ast import AssertStmt
from .ast import AssignStmt
from .ast import BinExpr
from .ast import BinOpKind
from .ast import Boolean
from .ast import CallStmt
from .ast import DeclType
from .ast import FromStmt
from .ast import IfStmt
from .ast import IterateStmt
from .ast import EmptyExpr
from .ast import LocalStmt
from .ast import PopStmt
from .ast import PushStmt
from .ast import SizeExpr
from .ast import TopExpr
from .ast import ArrayExpr
from .ast import Lval
from .ast import LvalExpr
from .ast import LvalField
from .ast import LvalIndex
from .ast import ModOp
from .ast import Number
from .ast import PrintsStmt
from .ast import Program
from .ast import SkipStmt
from .ast import SwapStmt
from .ast import UnaryExpr
from .ast import UnaryOpKind
from .ast import UncallStmt
from .invert import invert_stmts

#: Program-counter value standing for "a Janus runtime assertion failed".
ERR_LOC = 0
#: Program-counter value standing for "the inlining bound was hit".
BOUND_LOC = 1
_FIRST_LOC = 2

#: Cut a block once its pending expressions get this large, so that a long
#: straight-line stretch cannot blow the term size up.
_BLOCK_CHARS = 4000

#: An array becomes one SMV variable per element, so a very long one would blow
#: the model up rather than fail; refuse instead of emitting it.
_MAX_ARRAY = 256

#: How deep a stack is modelled.  A Janus stack is unbounded, so a finite model
#: has to stop somewhere; a run that pushes past this leaves for BOUND, exactly
#: as a call deeper than `max_depth` does.  So a proof of `pc != ERR` is about
#: the runs that stay within the depth, and proving `pc != BOUND` too is what
#: makes it unconditional (§6).  Measured: only 2 of the 32 corpus programs
#: that touch a stack have a statically justifiable depth (§17), which is why
#: this is a bound rather than a claim.
_STACK_DEPTH = 8

#: A source name resolves to one SMV variable (a scalar), to the tuple of its
#: elements' variables (an expanded array), or to a mapping from field name to
#: either of those (an expanded struct).  A struct field has no struct type of
#: its own in this dialect's corpus, so the nesting stops there.
_Env = dict  # dict[str, str | tuple[str, ...] | dict[str, str | tuple[str, ...]]]

#: Reserved in SMV (plus `pc`, which names the program counter).  A Janus
#: variable with one of these names is renamed, the way `c_codegen.py` renames
#: identifiers that collide with C++ keywords.
#:
#: The single letters are the temporal and epistemic operators of nuXmv's logic
#: — `A`, `E`, `X`, `U`, `T`, `K`, … — and they are the ones that actually bite:
#: `knapsack_c.ja` declares `K` and `bwt_inverse_c.ja` declares `T`, and
#: both produced a model nuXmv refused to read.  The list below was obtained by
#: **probing the binary** with a one-variable model, not by reading a grammar;
#: `K` is reserved by nuXmv without appearing in NuSMV's published one.
#: `tests/verify/test_smv_reserved.py` pins the probed set.
_SMV_RESERVED = frozenset({
    "pc", "MODULE", "VAR", "IVAR", "FROZENVAR", "DEFINE", "MDEFINE", "ASSIGN",
    "INIT", "TRANS", "INVAR", "INVARSPEC", "CTLSPEC", "LTLSPEC", "PSLSPEC",
    "SPEC", "FAIRNESS", "JUSTICE", "COMPASSION", "CONSTANTS", "CONSTARRAY",
    "COMPUTE", "ISA", "case", "esac", "init", "next", "self", "TRUE", "FALSE",
    "boolean", "integer", "real", "word", "array", "of", "in", "union", "xor",
    "xnor", "mod", "process", "abs", "max", "min", "MIN", "MAX", "ABS",
    "count", "toint", "bool", "floor", "sizeof", "signed", "unsigned",
    "extend", "resize", "swconst", "uwconst", "word1", "not", "and", "or",
    # temporal / epistemic operators
    "A", "E", "F", "G", "H", "K", "O", "S", "T", "U", "V", "X", "Y", "Z",
    "EX", "AX", "EF", "AF", "EG", "AG", "BU", "EBF", "ABF", "EBG", "ABG",
    # transcendental functions and misc, found the same way —
    # `arith_roundtrip_c.ja` declares `exp`, which the corpus-wide malformed
    # check in `test_smv_reserved.py` caught the moment `iterate` let it in.
    "exp", "ln", "sin", "cos", "tan", "pow", "sqrt", "READ", "WRITE", "typeof",
})

_ARITH = {BinOpKind.ADD: "+", BinOpKind.SUB: "-", BinOpKind.MUL: "*"}
_COMPARE = {
    BinOpKind.GT: ">",
    BinOpKind.LT: "<",
    BinOpKind.GE: ">=",
    BinOpKind.LE: "<=",
    BinOpKind.EQ: "=",
    BinOpKind.NEQ: "!=",
}


class SmvUnsupported(Exception):
  """A construct outside the scalar fragment; the caller must not proceed."""


#: Diagnostic only.  When this holds a list, `_stmts` records a statement's
#: rejection and moves on to the next statement instead of aborting the whole
#: compilation, so one run reports EVERY reason a program is out of the
#: fragment rather than only the first one it hits.
#:
#: Why that distinction matters here: the blocker tallies this project uses to
#: size a feature ("18 programs are stopped by `^=`") count FIRST reasons, and
#: a first-reason tally is not even an upper bound on what implementing that
#: feature would admit — a program may hold any number of blockers.  Estimates
#: built on those tallies missed three times out of four (docs/loop-queue.md,
#: items 21-28).
#:
#: The model produced under collection is GARBAGE — a skipped statement leaves
#: the compiler's state inconsistent, and later statements may fail for reasons
#: that are only fallout from the skip.  `collect_unsupported` therefore throws
#: the model away, and nothing else may set this.
_COLLECT: list[str] | None = None


@dataclass(frozen=True)
class _Stack:
  """A stack: `depth` cells plus the count of how many are live.

  Kept distinct from an array's plain tuple of cells because the two are read
  differently — an array cell is named by the program, a stack cell only ever
  by the count — and because binding a formal to a stack must carry the count
  along with the cells.
  """
  cells: tuple[str, ...]
  count: str
  depth: int


@dataclass(frozen=True)
class _Trans:
  src: int
  guard: str
  updates: tuple[tuple[str, str], ...]
  dst: int


class _Compiler:
  def __init__(self, program: Program, init: str, assume: str | None, max_depth: int,
               style: str = "trans", arrays: str = "native"):
    if program.main is None:
      raise SmvUnsupported("no main procedure")
    self.program = program
    self.procs = {p.procname.name: p for p in program.procs}
    self.structs = {sd.ident.name: sd for sd in (program.struct_defs or [])}
    self.init_mode = init
    self.assume = assume
    self.max_depth = max_depth
    self.style = style
    self.arrays_mode = arrays
    #: `(name, size)` for every array declared with nuXmv's own array type.
    self.array_decls: list[tuple[str, int]] = []
    #: cell name -> the array it belongs to, so a read can use `a[i]` directly.
    self.array_of: dict[str, str] = {}
    #: Base names of the native array declarations handed out so far.  They
    #: never reach `varnames` — only their *cells* (`a[0]`, `a[1]`, …) do — so
    #: `_uniq` cannot see them there and would hand the same base out twice.
    #: One model can genuinely declare the same array name twice: composing a
    #: program with its own inverse (`equiv_smv`) inlines each `local` twice,
    #: and nuXmv then refuses the model with "multiple declaration of
    #: identifier".  The scalar path never had this because `_declare` appends
    #: the name itself.
    self.array_bases: set[str] = set()
    #: cell tuple -> its shape.  Cells are stored flat in row-major order, so a
    #: rank-2 array is a tuple of `rows * cols` names; the shape is what lets
    #: `A[i][j]` fold to one offset *and* lets each index be checked against its
    #: own dimension.  Without it `A[0][5]` on a 2x3 array would pass, its flat
    #: offset 5 being inside the six cells.  Absent means rank 1.
    self.dims: dict[tuple[str, ...], tuple[int, ...]] = {}
    self.varnames: list[str] = []
    self.var_init: dict[str, str | None] = {}
    self.defines: list[tuple[str, str]] = []
    self.trans: list[_Trans] = []
    self._next_loc = _FIRST_LOC
    self._uid = 0
    self.uses_err = False
    self.uses_bound = False
    # The symbolic state of the block currently being accumulated.
    self.loc = self._loc()
    self.pending: dict[str, str] = {}
    self.path: list[str] = []

  # -- names and locations ---------------------------------------------

  def _loc(self) -> int:
    loc = self._next_loc
    self._next_loc += 1
    return loc

  def _uniq(self, base: str) -> str:
    name = f"{base}_" if base in _SMV_RESERVED else base
    while name in self.varnames or name in self.array_bases:
      self._uid += 1
      name = f"{base}__{self._uid}"
    return name

  def _declare(self, base: str, init: str | None) -> str:
    name = self._uniq(base)
    self.varnames.append(name)
    self.var_init[name] = init
    return name

  @staticmethod
  def _conj(parts: list[str]) -> str:
    parts = [p for p in parts if p != "TRUE"]
    if not parts:
      return "TRUE"
    return " & ".join(f"({p})" for p in parts)

  # -- the block being accumulated -------------------------------------

  def _val(self, name: str) -> str:
    """The value of `name` at this point, as an expression over block entry."""
    return self.pending.get(name, name)

  def _edge(self, guard: str, dst: int) -> None:
    """Leave the current block by `guard`, carrying its pending updates."""
    updates = tuple((n, e) for n, e in self.pending.items() if e != n)
    self.trans.append(_Trans(self.loc, self._conj(self.path + [guard]), updates, dst))

  def _err(self, guard: str) -> None:
    """Leave for ERR by `guard`; ERR is absorbing, so no updates are needed."""
    self.uses_err = True
    self.trans.append(_Trans(self.loc, self._conj(self.path + [guard]), (), ERR_LOC))

  def _check(self, obligations: list[str]) -> None:
    """Fail to ERR unless every obligation holds, then assume that it does."""
    for obligation in obligations:
      if obligation == "TRUE":
        continue
      self._err(f"!({obligation})")
      self.path.append(obligation)

  def _unconditional_error(self) -> None:
    """Reaching this statement is itself the error.

    Three run-time checks land here — an aliasing violation, a `local`/`delocal`
    name mismatch, and an out-of-bounds constant index.  None of them is a gap in
    the translation: PyJanus executes the statement and raises.  So the edge to
    ERR is unconditional and the continuation is emitted at a location nothing
    enters.
    """
    self._err("TRUE")
    self._enter(self._loc())

  def _enter(self, dst: int) -> None:
    self.loc = dst
    self.pending = {}
    self.path = []

  def _seal(self, dst: int | None = None) -> int:
    """Cut the block here, emitting it as one transition."""
    if dst is None:
      if not self.pending and not self.path:
        return self.loc
      dst = self._loc()
    self._edge("TRUE", dst)
    self._enter(dst)
    return dst

  def _maybe_seal(self) -> None:
    if sum(len(e) for e in self.pending.values()) > _BLOCK_CHARS:
      self._seal()

  # -- expressions -----------------------------------------------------

  def _div_defines(self, a: str, b: str) -> tuple[str, str]:
    """DEFINEs for Python-style floor division and modulo of `a` by `b`.

    nuXmv's `/` truncates toward zero, so the quotient is corrected by one when
    the truncating remainder and the divisor have opposite signs.  The macros
    are made total (returning 0 when `b` is 0) so that the SMT engine never
    sees a division by zero in states the guards exclude anyway.
    """
    i = self._uid
    self._uid += 1
    tq, tr, fq, fr = f"__tq{i}", f"__tr{i}", f"__fq{i}", f"__fr{i}"
    self.defines.append((tq, f"case ({b}) = 0 : 0; TRUE : ({a}) / ({b}); esac"))
    self.defines.append((tr, f"({a}) - ({b}) * {tq}"))
    self.defines.append(
        (fq, f"case {tr} = 0 : {tq}; ({tr} < 0) <-> (({b}) < 0) : {tq}; TRUE : {tq} - 1; esac"))
    self.defines.append((fr, f"({a}) - ({b}) * {fq}"))
    return fq, fr

  def _occurs(self, name: str, e, env: dict[str, str]) -> bool:
    """Does the SMV variable `name` occur in `e` after resolving through `env`?

    **Fail-closed.**  A node this does not understand raises rather than
    answering "no".  The set accepted here is exactly the set `_iexpr` and
    `_bexpr` accept, so the aliasing check and the translation refuse together.

    That lockstep is the point.  The swap gap had this shape: `_stmt` grew a
    case, the aliasing check did not, and the model silently said "no alias
    here".  Ending in `return False` reproduces it one level down — a ternary or
    a stack `top` would read as "the target does not occur", and the only reason
    that was harmless is that `_iexpr` happens to refuse those nodes a moment
    later.  Safety must not rest on the order two unrelated functions fail in.

    `or` short-circuits, so a `True` on the left returns without examining the
    right.  That is safe: `True` is already the conservative answer and it is
    also the faithful one, since PyJanus reports the alias at this statement.
    """
    if isinstance(e, (Number, Boolean)):
      return False
    if isinstance(e, LvalExpr):
      return self._occurs_lval(name, e.lval, env)
    if isinstance(e, BinExpr):
      return self._occurs(name, e.left, env) or self._occurs(name, e.right, env)
    if isinstance(e, UnaryExpr):
      return self._occurs(name, e.expr, env)
    if isinstance(e, (TopExpr, SizeExpr, EmptyExpr)):
      # The target of an assignment is a scalar l-value; a stack's cells and
      # count are separate model variables that no scalar name can reach.  So
      # `x += top(s)` cannot alias, and this is False rather than fail-closed.
      # (`push`/`pop` do not come through here — they have their own encoders.)
      return False
    raise SmvUnsupported(
        f"expression outside the fragment in an aliasing check: {type(e).__name__}")

  def _index_expr(self, lval, env: _Env) -> list:
    """The index expressions of an l-value, **after** the field selector.

    `b.v[i]` indexes the field, so the raw `selectors[0]` is the field and using
    it as an index reads the wrong node.  Everything that needs the indices goes
    through here.  A rank-2 array has two of them.
    """
    _, selectors = self._base_of(lval, env)
    return [sel.expr for sel in selectors if isinstance(sel, LvalIndex)]

  def _shape(self, entry: tuple) -> tuple[int, ...]:
    """The declared shape of a cell tuple; rank 1 unless registered."""
    return self.dims.get(entry, (len(entry),))

  def _strides(self, shape: tuple[int, ...]) -> list[int]:
    """Row-major strides: the last index moves one cell."""
    strides, step = [], 1
    for size in reversed(shape):
      strides.insert(0, step)
      step *= size
    return strides

  def _flat_index(self, entry: tuple, selectors, env: _Env, obl: list[str]) -> str:
    """Fold every index selector into one row-major offset into `entry`.

    Each index is checked against **its own** dimension rather than against the
    flat length, which is the whole reason the shape is kept: `A[0][5]` on a 2x3
    array has offset 5, inside the six cells and outside the array.
    """
    shape = self._shape(entry)
    if len(selectors) != len(shape) or not all(
        isinstance(sel, LvalIndex) for sel in selectors):
      raise SmvUnsupported(
          f"index of rank {len(selectors)} on an array of rank {len(shape)}")
    strides = self._strides(shape)
    indices = [sel.expr for sel in selectors]
    if all(isinstance(index, Number) for index in indices):
      return str(sum(i.value * s for i, s in zip(indices, strides)))
    parts = []
    for index, size, stride in zip(indices, shape, strides):
      term = self._iexpr(index, env, obl)
      obl.append(f"({term}) >= 0")
      obl.append(f"({term}) < {size}")
      # `_iexpr` already parenthesises, so rank 1 gives back exactly the term
      # the single-index encoding used to produce.
      parts.append(term if stride == 1 else f"({term} * {stride})")
    return parts[0] if len(parts) == 1 else "(" + " + ".join(parts) + ")"

  def _cell_index(self, lval, env: _Env, obl: list[str]) -> tuple | None:
    """`(elements, index term)` when this l-value is an array cell, else `None`.

    A constant index yields its own literal, so the two kinds compose: an
    aliasing question between a constant and a variable index is the same
    equality as between two variables, just with one side decided.
    """
    entry, selectors = self._base_of(lval, env)
    if not isinstance(entry, tuple):
      return None
    return entry, self._flat_index(entry, selectors, env, obl)

  def _alias_obl(self, entry: tuple, tidx: str, e, env: _Env, obl: list[str]) -> bool:
    """Require every cell of `entry` read by `e` to differ from index `tidx`.

    `a[i] += a[j]` fails **exactly when i = j** — the index-precise condition
    `RevArr.wf_assign` formalises, which admits `A[j][i] += A[j][k]` for i != k
    where a name-based check would not.  It is a *term*, so it becomes an
    obligation checked into ERR, not a refusal (which would lose the program)
    and not a blanket error (which would be a false alarm).

    Returns True when the alias is *decided* — both indices constant and equal —
    in which case reaching the statement is itself the error.
    """
    if isinstance(e, (Number, Boolean)):
      return False
    if isinstance(e, LvalExpr):
      cell = self._cell_index(e.lval, env, obl)
      if cell is None:
        return False
      ridx = cell[1]
      inner = self._index_expr(e.lval, env)
      # Forced, not short-circuited: every index contributes its obligations.
      nested = any([self._alias_obl(entry, tidx, index, env, obl) for index in inner])
      if cell[0] is not entry:
        # a different array cannot alias, but its index may still read this one
        return nested
      if tidx.isdigit() and ridx.isdigit():
        if tidx == ridx:
          return True
      else:
        obl.append(f"({tidx}) != ({ridx})")
      return nested
    if isinstance(e, BinExpr):
      left = self._alias_obl(entry, tidx, e.left, env, obl)
      return self._alias_obl(entry, tidx, e.right, env, obl) or left
    if isinstance(e, UnaryExpr):
      return self._alias_obl(entry, tidx, e.expr, env, obl)
    raise SmvUnsupported(
        f"expression outside the fragment in an aliasing check: {type(e).__name__}")

  def _occurs_lval(self, name: str, lval, env: _Env) -> bool:
    """Does the SMV variable `name` occur in this l-value?

    A variable index reads *the index expression* as well as the array, which is
    what PyJanus's `_selector_index_exprs` walks.  When the target is a cell of
    the same array the answer is not syntactic — `a[0] += a[i]` fails exactly
    when `i = 0` — so it is refused rather than guessed: answering "yes" would be
    a false alarm and "no" would be unsound.  Deciding it needs the
    index-precise test `RevArr.wf_assign` formalises.
    """
    entry, selectors = self._base_of(lval, env)
    if not selectors:
      if isinstance(entry, tuple):
        raise SmvUnsupported(f"whole-array l-value: {lval.ident.name}")
      return entry == name
    if not isinstance(entry, tuple):
      raise SmvUnsupported(f"indexing a non-array: {lval.ident.name}")
    shape = self._shape(entry)
    if len(selectors) != len(shape) or not all(
        isinstance(sel, LvalIndex) for sel in selectors):
      raise SmvUnsupported(
          f"index of rank {len(selectors)} on an array of rank {len(shape)}")
    indices = [sel.expr for sel in selectors]
    if all(isinstance(index, Number) for index in indices):
      if any(not 0 <= index.value < size for index, size in zip(indices, shape)):
        return False
      flat = sum(i.value * s for i, s in zip(indices, self._strides(shape)))
      return entry[flat] == name
    if name in entry:
      raise SmvUnsupported(
          "aliasing between a cell and a variable index of the same array")
    return any(self._occurs(name, index, env) for index in indices)

  def _lookup(self, name: str, env: dict[str, str]) -> str:
    if name not in env:
      raise SmvUnsupported(f"variable out of the fragment: {name}")
    return env[name]

  def _base_of(self, lval, env: _Env):
    """Strip a leading field selector, giving `(entry, remaining selectors)`.

    A struct is one entry per field, so `p.x` resolves the field first and then
    behaves exactly like a scalar or array named `p_x`.
    """
    entry = self._lookup(lval.ident.name, env)
    selectors = list(lval.selectors)
    if isinstance(entry, dict):
      # An array of structs is kept as *field -> tuple over elements*, so the
      # field selector comes **after** the index in `p[i].a` and before it in
      # `p.a[i]`.  Take whichever position it is in; what remains indexes the
      # tuple the field names, which is the ordinary array path.
      at = next((k for k, sel in enumerate(selectors)
                 if isinstance(sel, LvalField)), None)
      if at is None:
        raise SmvUnsupported(f"whole-struct l-value: {lval.ident.name}")
      field = selectors.pop(at).ident.name
      if field not in entry:
        raise SmvUnsupported(f"no such field: {lval.ident.name}.{field}")
      return entry[field], selectors
    if selectors and isinstance(selectors[0], LvalField):
      raise SmvUnsupported(f"field of a non-struct: {lval.ident.name}")
    return entry, selectors

  def _lval_name(self, lval, env: _Env) -> str:
    # A stack is not a scalar l-value.  Without this the `_Stack` object walked
    # into the scalar path and its repr was emitted into the model, which nuXmv
    # then refused to read — a `model-error`, i.e. a question never asked
    # dressed as one that was.  `type-error-swap.ja` found it.
    if isinstance(env.get(getattr(lval.ident, "name", None)), _Stack) \
        and not lval.selectors:
      raise SmvUnsupported(f"a stack used where a scalar is expected: {lval.ident.name}")
    """The SMV variable an l-value denotes.

    A scalar denotes its own variable; an expanded array denotes one element,
    named by a **constant** index.  A variable index needs a `case` over the
    elements and is not translated yet.
    """
    entry, selectors = self._base_of(lval, env)
    if not selectors:
      if isinstance(entry, tuple):
        raise SmvUnsupported(f"whole-array l-value: {lval.ident.name}")
      return entry
    if not isinstance(entry, tuple):
      raise SmvUnsupported(f"indexing a non-array: {lval.ident.name}")
    shape = self._shape(entry)
    if len(selectors) != len(shape) or not all(
        isinstance(sel, LvalIndex) for sel in selectors):
      raise SmvUnsupported(
          f"index of rank {len(selectors)} on an array of rank {len(shape)}")
    indices = [sel.expr for sel in selectors]
    if not all(isinstance(index, Number) for index in indices):
      raise SmvUnsupported("variable array index")
    if any(not 0 <= index.value < size for index, size in zip(indices, shape)):
      # The caller checks bounds first, so this is defensive only.
      raise SmvUnsupported(f"index out of bounds: {lval.ident.name}")
    flat = sum(i.value * s for i, s in zip(indices, self._strides(shape)))
    return entry[flat]

  def _oob_lval(self, lval, env: _Env) -> bool:
    """Is a *constant* index outside its own dimension?

    PyJanus raises "Array index `[5]' was out of bounds" when it reaches such a
    statement, so reaching it is the error.  A variable index is not decided
    here — it becomes an obligation in `_flat_index`.

    The check is **per dimension**, not against the flat length: on a 2x3 array
    `A[0][5]` folds to offset 5, which is inside the six cells.
    """
    if lval.ident.name not in env:
      return False
    entry, selectors = self._base_of(lval, env)
    if not isinstance(entry, tuple) or not selectors:
      return False
    shape = self._shape(entry)
    for selector, size in zip(selectors, shape):
      if not isinstance(selector, LvalIndex):
        return False
      if not isinstance(selector.expr, Number):
        # a nested constant index may still be out of bounds
        if self._oob(selector.expr, env):
          return True
      elif not 0 <= selector.expr.value < size:
        return True
    return False

  def _oob(self, e, env: _Env) -> bool:
    """The same question for every l-value in an expression.  Fail-closed on a
    node outside the fragment, so this and `_iexpr` refuse the same set."""
    if isinstance(e, (Number, Boolean)):
      return False
    if isinstance(e, LvalExpr):
      return self._oob_lval(e.lval, env)
    if isinstance(e, BinExpr):
      return self._oob(e.left, env) or self._oob(e.right, env)
    if isinstance(e, UnaryExpr):
      return self._oob(e.expr, env)
    if isinstance(e, (TopExpr, SizeExpr, EmptyExpr)):
      # A stack expression carries no constant index to be out of range.  `top`
      # on an empty stack IS an error, but a run-time one whose obligation
      # `_iexpr` emits — this pre-check is only for indices decidable now.
      return False
    raise SmvUnsupported(
        f"expression outside the fragment in a bounds check: {type(e).__name__}")

  def _read_lval(self, lval, env: _Env, obl: list[str]) -> str:
    """Read an l-value.  A variable index becomes a `case` over the elements.

    The index is itself translated (so it reads the pending map, keeping the
    large-block composition right) and its range becomes an **obligation**, not
    an assumption: PyJanus raises "Array index `[i]' was out of bounds" when it
    reaches such a read, so out-of-range has to reach ERR.

    The last element is the `TRUE` default rather than a branch of its own, which
    is exactly the case the bounds obligation leaves; a one-element array needs
    no `case` at all.
    """
    entry, selectors = self._base_of(lval, env)
    if not selectors:
      if isinstance(entry, tuple):
        raise SmvUnsupported(f"whole-array l-value: {lval.ident.name}")
      return self._val(entry)
    if not isinstance(entry, tuple):
      raise SmvUnsupported(f"indexing a non-array: {lval.ident.name}")
    idx = self._flat_index(entry, selectors, env, obl)
    if idx.isdigit():
      return self._val(entry[int(idx)])
    return self._read_at(entry, idx)

  def _read_at(self, entry: tuple, idx: str) -> str:
    """The value of the selected element.

    With nuXmv's array type this is just `a[i]` — one token — provided no
    element is still pending in this block.  Otherwise, and always in the
    expanded encoding, it is a `case` over the elements, which copies every
    element's pending term and is where the model size comes from (§5.6).
    """
    base = self.array_of.get(entry[0])
    if base is not None and not any(name in self.pending for name in entry):
      return f"{base}[{idx}]"
    if len(entry) == 1:
      return self._val(entry[0])
    branches = "".join(f"{idx} = {i} : {self._val(entry[i])}; "
                       for i in range(len(entry) - 1))
    return f"(case {branches}TRUE : {self._val(entry[-1])}; esac)"

  def _iexpr(self, e, env: dict[str, str], obl: list[str]) -> str:
    """Translate an integer-sorted expression, appending safety obligations."""
    if isinstance(e, Number):
      return str(e.value) if e.value >= 0 else f"({e.value})"
    if isinstance(e, LvalExpr):
      return self._read_lval(e.lval, env, obl)
    if isinstance(e, (TopExpr, SizeExpr, EmptyExpr)):
      entry = env.get(e.ident.name)
      if isinstance(e, SizeExpr) and isinstance(entry, tuple):
        # `size` is the one that is polymorphic: PyJanus accepts an ARRAY as
        # well as a stack ("Couldn't match expected type `array' or `stack'").
        # Refusing it turned `perm_to_code_c.ja` — which runs — into `refuted`,
        # a false alarm found by re-scanning the corpus.
        return str(len(entry))
      if not isinstance(entry, _Stack):
        # `top(x)` on a non-stack: PyJanus raises "Couldn't match expected type
        # `stack'" when it reaches the expression, so reaching it is the error.
        # An always-false obligation is how an *expression* reaches ERR.
        obl.append("FALSE")
        return "0"
      st = self._stack_of(e.ident.name, env)
      count = self._val(st.count)
      if isinstance(e, SizeExpr):
        return f"({count})"
      if isinstance(e, EmptyExpr):
        # `empty(s)` is usable as an integer: measured 1 on an empty stack (§19).
        return f"(case {count} = 0 : 1; TRUE : 0; esac)"
      # `top` does not consume — but it fails on an empty stack with the very
      # message `pop` gives, so it is an EXPRESSION carrying an ERR edge (§19).
      obl.append(f"{count} > 0")
      return self._read_at(st.cells, f"({count} - 1)")
    if isinstance(e, BinExpr):
      if e.op in _ARITH:
        left = self._iexpr(e.left, env, obl)
        right = self._iexpr(e.right, env, obl)
        return f"({left} {_ARITH[e.op]} {right})"
      if e.op in (BinOpKind.DIV, BinOpKind.MOD):
        left = self._iexpr(e.left, env, obl)
        right = self._iexpr(e.right, env, obl)
        obl.append(f"({right}) != 0")
        quotient, remainder = self._div_defines(left, right)
        return quotient if e.op is BinOpKind.DIV else remainder
      raise SmvUnsupported(f"integer operator outside the fragment: {e.op.value}")
    raise SmvUnsupported(f"integer expression outside the fragment: {type(e).__name__}")

  def _bexpr(self, e, env: dict[str, str], obl: list[str]) -> str:
    """Translate a boolean-sorted expression; mixing the sorts is refused."""
    if isinstance(e, Boolean):
      return "TRUE" if e.value else "FALSE"
    if isinstance(e, UnaryExpr):
      if e.op is UnaryOpKind.NOT:
        return f"!({self._bexpr(e.expr, env, obl)})"
      raise SmvUnsupported(f"unary operator outside the fragment: {e.op.value}")
    if isinstance(e, BinExpr):
      if e.op in _COMPARE:
        left = self._iexpr(e.left, env, obl)
        right = self._iexpr(e.right, env, obl)
        return f"({left} {_COMPARE[e.op]} {right})"
      if e.op is BinOpKind.LAND:
        return f"({self._bexpr(e.left, env, obl)} & {self._bexpr(e.right, env, obl)})"
      if e.op is BinOpKind.LOR:
        return f"({self._bexpr(e.left, env, obl)} | {self._bexpr(e.right, env, obl)})"
    if isinstance(e, EmptyExpr):
      # `if !empty(s)` is how the corpus branches on a stack (`reverse`).  It is
      # boolean here and an integer in `_iexpr`; Janus lets it be both, so both
      # sorts translate it rather than one refusing.
      if not isinstance(env.get(e.ident.name), _Stack):
        obl.append("FALSE")     # type error at run time; same as `_iexpr`
        return "FALSE"
      return f"({self._val(self._stack_of(e.ident.name, env).count)} = 0)"
    raise SmvUnsupported(f"condition outside the fragment: {type(e).__name__}")

  def _cond(self, e, env: dict[str, str]) -> str:
    """A condition, with its evaluation obligations already checked into ERR."""
    obl: list[str] = []
    text = self._bexpr(e, env, obl)
    self._check(obl)
    return text

  # -- statements ------------------------------------------------------

  def _stmts(self, stmts, env: dict[str, str], depth: int) -> None:
    for stmt in stmts:
      if _COLLECT is None:
        self._stmt(stmt, env, depth)
        continue
      try:                                  # diagnostic mode; see _COLLECT
        self._stmt(stmt, env, depth)
      except SmvUnsupported as exc:
        _COLLECT.append(str(exc))

  def _stmt(self, s, env: dict[str, str], depth: int) -> None:
    if isinstance(s, SkipStmt):
      return
    if isinstance(s, PrintsStmt):
      return self._prints(s, env)
    if isinstance(s, AssignStmt):
      if self._oob_lval(s.lval, env) or self._oob(s.expr, env):
        return self._unconditional_error()
      return self._assign(s, env)
    if isinstance(s, SwapStmt):
      if self._oob_lval(s.left, env) or self._oob_lval(s.right, env):
        return self._unconditional_error()
      if isinstance(env.get(s.left.ident.name), _Stack) \
          or isinstance(env.get(s.right.ident.name), _Stack):
        # `x <=> s` — PyJanus: "Can't swap variables of type `int' and `stack'".
        # Reaching the statement is the error.
        return self._unconditional_error()
      lentry, _ = self._base_of(s.left, env)
      rentry, _ = self._base_of(s.right, env)
      if isinstance(lentry, tuple) or isinstance(rentry, tuple):
        if not (isinstance(lentry, tuple) and isinstance(rentry, tuple)):
          raise SmvUnsupported("swap between a scalar and an array cell")
        return self._swap_cells(s, env, lentry, rentry)
      left = self._lval_name(s.left, env)
      right = self._lval_name(s.right, env)
      if left == right:
        # The same run-time check as an assignment's, and the same reason it
        # cannot be skipped: symbolic execution of `x <=> x` exchanges one
        # pending entry with itself, i.e. models as the *identity* a statement
        # PyJanus rejects (`_check_alias_swap`).  Reaching it is the error.
        self._unconditional_error()
        return
      before_left, before_right = self._val(left), self._val(right)
      self.pending[left], self.pending[right] = before_right, before_left
      return
    if isinstance(s, PushStmt):
      return self._push(s, env)
    if isinstance(s, PopStmt):
      return self._pop(s, env)
    if isinstance(s, AssertStmt):
      if self._oob(s.expr, env):
        return self._unconditional_error()
      self._check([self._cond(s.expr, env)])
      return
    if isinstance(s, IfStmt):
      return self._if(s, env, depth)
    if isinstance(s, FromStmt):
      return self._from(s, env, depth)
    if isinstance(s, IterateStmt):
      return self._iterate(s, env, depth)
    if isinstance(s, LocalStmt):
      return self._local(s, env, depth)
    if isinstance(s, (CallStmt, UncallStmt)):
      return self._call(s, env, depth, isinstance(s, UncallStmt))
    raise SmvUnsupported(f"statement outside the fragment: {type(s).__name__}")

  #: What `runtime._check_printf_type` accepts, restricted to the fragment.
  #: Only `int` and `int array` can be declared here — a `bool`, a stack or a
  #: char array is refused at its declaration — so `%b`, `%s` and `%t` have no
  #: well-typed argument at all and always fail.
  _PRINTF_KINDS = {"d": "int", "a": "array"}

  def _arg_kind(self, arg, env: _Env) -> str | None:
    """`"int"` / `"array"` for an output argument; `None` if it does not resolve."""
    name = arg.ident.name if isinstance(arg, Lval) else getattr(arg, "name", None)
    if name is None or name not in env:
      return None  # PyJanus raises when it tries to resolve it
    if not isinstance(arg, Lval):
      return "array" if isinstance(env[name], tuple) else "int"
    entry, rest = self._base_of(arg, env)
    if isinstance(entry, tuple):
      return "int" if rest else "array"
    return "int"

  def _prints(self, s: PrintsStmt, env: _Env) -> None:
    """An output statement leaves the store alone — but it can still fail.

    Returning early for all of them let the checker *prove safe* five error
    fixtures PyJanus rejects (a `printf` that does not match its format, a
    `show` of an undeclared name).  Those failures do not depend on the store,
    so reaching the statement is the error and the edge to ERR is
    unconditional — the same shape as a `delocal` name mismatch (§3.3).
    """
    prints = s.prints
    if prints.reversible or prints.kind in ("read", "scanf"):
      # An input statement makes the next store depend on stdin.  The model has
      # no way to represent that, so it refuses rather than answers.
      raise SmvUnsupported(f"input statement: {prints.kind}")
    if prints.kind == "print":
      return  # a literal string, with nothing to resolve
    kinds: list[str] = []
    for arg in prints.args:
      if isinstance(arg, Lval) and arg.ident.name in env and self._oob_lval(arg, env):
        return self._unconditional_error()  # printing a cell is still a read
      kind = self._arg_kind(arg, env)
      if kind is None:
        return self._unconditional_error()
      kinds.append(kind)
    if prints.kind != "printf":
      return  # `show` and `write` only need their arguments to resolve
    text, used, i = prints.text or "", 0, 0
    while i < len(text):
      if text[i] == "%" and i + 1 < len(text):
        spec = text[i + 1]
        if spec != "%":
          if used >= len(kinds) or self._PRINTF_KINDS.get(spec) != kinds[used]:
            return self._unconditional_error()
          used += 1
        i += 2
      else:
        i += 1
    if used != len(kinds):
      return self._unconditional_error()

  def _assign(self, s: AssignStmt, env: _Env) -> None:
    entry, _ = self._base_of(s.lval, env)
    if isinstance(entry, tuple):
      return self._assign_cell(s, env, entry)
    target = self._lval_name(s.lval, env)
    if self._occurs(target, s.expr, env):
      # `x += x` is not injective, and Janus rejects it *at run time* — after
      # inlining, `call bar(x, x); a += b` resolves to exactly this.  Reaching
      # the statement is the error, so it becomes an unconditional edge to ERR.
      self._unconditional_error()
      return
    obl: list[str] = []
    rhs = self._iexpr(s.expr, env, obl)
    new = self._apply(s.mod_op, self._val(target), rhs, obl)
    self._check(obl)
    self.pending[target] = new
    self._maybe_seal()

  def _apply(self, mod_op, old: str, rhs: str, obl: list[str]) -> str:
    """`old op= rhs`, with the operator's own run-time obligations."""
    if mod_op is ModOp.ADD_EQ:
      return f"({old} + {rhs})"
    if mod_op is ModOp.SUB_EQ:
      return f"({old} - {rhs})"
    if mod_op is ModOp.MUL_EQ:
      obl.append(f"({rhs}) != 0")  # x *= 0 is not injective
      return f"({old} * {rhs})"
    if mod_op is ModOp.DIV_EQ:
      obl.append(f"({rhs}) != 0")
      quotient, remainder = self._div_defines(old, rhs)
      obl.append(f"{remainder} = 0")  # `/=` must divide exactly
      return quotient
    raise SmvUnsupported(f"assignment operator outside the fragment: {mod_op.value}")

  def _assign_cell(self, s: AssignStmt, env: _Env, entry: tuple) -> None:
    """`a[t] op= e`, with `t` constant or variable.

    The aliasing condition is the same equality either way; only the update
    differs, and a constant index updates one element rather than all of them.
    """
    obl: list[str] = []
    cell = self._cell_index(s.lval, env, obl)
    assert cell is not None
    tidx = cell[1]
    definite = self._alias_obl(entry, tidx, s.expr, env, obl)
    for index in self._index_expr(s.lval, env):
      if self._alias_obl(entry, tidx, index, env, obl):
        definite = True
    if definite:
      return self._unconditional_error()
    rhs = self._iexpr(s.expr, env, obl)
    if tidx.isdigit():
      target = entry[int(tidx)]
      new = self._apply(s.mod_op, self._val(target), rhs, obl)
      self._check(obl)
      self.pending[target] = new
    else:
      new = self._apply(s.mod_op, self._read_at(entry, tidx), rhs, obl)
      self._check(obl)
      before = [self._val(name) for name in entry]
      for k, name in enumerate(entry):
        self.pending[name] = f"(case {tidx} = {k} : {new}; TRUE : {before[k]}; esac)"
      if self.arrays_mode == "native":
        # Commit now, so a later read is `a[i]` rather than a case over the
        # pending terms.  Trades locations for term size -- the tradeoff §5.4
        # measured, in the direction §5.6 says matters here.
        self._seal()
        return
    self._maybe_seal()

  def _swap_cells(self, s, env: _Env, left: tuple, right: tuple) -> None:
    """`a[i] <=> b[j]`: simultaneous, with the aliasing equality as an obligation
    when both sides are the same array."""
    obl: list[str] = []
    lcell = self._cell_index(s.left, env, obl)
    rcell = self._cell_index(s.right, env, obl)
    assert lcell is not None and rcell is not None
    lidx, ridx = lcell[1], rcell[1]
    definite = False
    if lcell[0] is rcell[0]:
      if lidx.isdigit() and ridx.isdigit():
        definite = lidx == ridx
      else:
        obl.append(f"({lidx}) != ({ridx})")
    # PyJanus's `_check_alias_swap` also compares every *index expression* of
    # either side against **both** keys: `a[0] <=> a[a[1]]` is an alias when
    # `a[1] = 1`, because the index reads the very cell being swapped.  Missing
    # this proved such a program safe.
    for index in self._index_expr(s.left, env) + self._index_expr(s.right, env):
      if self._alias_obl(left, lidx, index, env, obl):
        definite = True
      if self._alias_obl(right, ridx, index, env, obl):
        definite = True
    if definite:
      return self._unconditional_error()
    self._check(obl)
    lval_now = self._read_at(left, lidx) if not lidx.isdigit() else self._val(left[int(lidx)])
    rval_now = self._read_at(right, ridx) if not ridx.isdigit() else self._val(right[int(ridx)])
    updates: dict[str, str] = {}
    if lidx.isdigit():
      updates[left[int(lidx)]] = rval_now
    else:
      for k, name in enumerate(left):
        updates[name] = f"(case {lidx} = {k} : {rval_now}; TRUE : {self._val(name)}; esac)"
    if ridx.isdigit():
      updates[right[int(ridx)]] = lval_now
    else:
      for k, name in enumerate(right):
        base = updates.get(name, self._val(name))
        updates[name] = f"(case {ridx} = {k} : {lval_now}; TRUE : {base}; esac)"
    self.pending.update(updates)
    self._maybe_seal()

  def _if(self, s: IfStmt, env: dict[str, str], depth: int) -> None:
    entry = self._cond(s.entry_cond, env)
    then_loc, else_loc, out = self._loc(), self._loc(), self._loc()
    self._edge(entry, then_loc)
    self._edge(f"!({entry})", else_loc)
    for branch, body, taken in ((then_loc, s.if_part, True), (else_loc, s.else_part, False)):
      self._enter(branch)
      self._stmts(body, env, depth)
      exit_cond = self._cond(s.exit_cond, env)
      self._check([exit_cond if taken else f"!({exit_cond})"])
      self._seal(out)
    self._enter(out)

  def _from(self, s: FromStmt, env: dict[str, str], depth: int) -> None:
    """`from e1 do S1 loop S2 until e2` = assert e1; S1; while !e2 { S2; assert !e1; S1 }."""
    self._check([self._cond(s.entry_cond, env)])
    top, out, again = self._loc(), self._loc(), self._loc()
    self._seal(top)

    self._stmts(s.do_part, env, depth)
    exit_cond = self._cond(s.exit_cond, env)
    self._edge(exit_cond, out)
    self._edge(f"!({exit_cond})", again)

    self._enter(again)
    self._stmts(s.loop_part, env, depth)
    self._check([f"!({self._cond(s.entry_cond, env)})"])
    self._seal(top)
    self._enter(out)

  def _iterate(self, s: IterateStmt, env: _Env, depth: int) -> None:
    """`iterate int i = a by t to b … end` — a counted loop, built as a CFG.

    Not a rewrite into `from`/`until`: a `from` loop runs its `do` part at least
    once, and `iterate int i = 0 to -1` runs its body **zero** times.  The shape
    is a head with a guard instead:

        i := a;  stop := b (+ t);  step := t
        head:  i != stop  ->  body; i += step; goto head
               i =  stop  ->  exit

    `stop` and `step` are **frozen into their own variables** because PyJanus
    evaluates both once, before the loop.  A body that permanently moves the
    variable the bound mentions must not change the trip count, so re-reading
    the expression on the back edge would be wrong.

    The loop variable shadows an outer one of the same name and disappears
    afterwards; `_declare` renames it, so the outer variable is untouched.

    A body that writes the loop variable can step over `stop`, and PyJanus then
    runs forever.  Here the exit is simply unreachable — non-termination is not
    an assertion failure (§6).
    """
    if s.typ.kind != "int":
      raise SmvUnsupported(f"non-int iterate variable: {s.ident.name}")
    obl: list[str] = []
    start = self._iexpr(s.start_expr, env, obl)
    step = self._iexpr(s.step_expr, env, obl)
    end = self._iexpr(s.end_expr, env, obl)
    self._check(obl)
    pin = "0" if self.init_mode == "zero" else None
    var = self._declare(s.ident.name, pin)
    stepv = self._declare(f"{s.ident.name}_step", pin)
    stopv = self._declare(f"{s.ident.name}_stop", pin)
    self.pending[var] = start
    self.pending[stepv] = step
    self.pending[stopv] = end if s.exclusive else f"({end} + {step})"

    top, body_loc, out = self._loc(), self._loc(), self._loc()
    self._seal(top)
    more = f"{self._val(var)} != {self._val(stopv)}"
    self._edge(more, body_loc)
    self._edge(f"!({more})", out)

    self._enter(body_loc)
    inner = dict(env)
    inner[s.ident.name] = var
    self._stmts(s.body, inner, depth)
    self.pending[var] = f"({self._val(var)} + {self._val(stepv)})"
    self._seal(top)
    self._enter(out)

  def _local(self, s: LocalStmt, env: dict[str, str], depth: int) -> None:
    enter, leave = s.enter_decl, s.exit_decl
    if enter.ident.name != leave.ident.name:
      # Another run-time check: PyJanus raises when it reaches the `delocal`.
      self._unconditional_error()
      return
    # What the *entry* declares has to be representable, or there is no local to
    # model.  Once it is, a `delocal` that disagrees about the type is the same
    # kind of run-time error as one that disagrees about the name.
    if enter.decl_type is DeclType.CONSTANT or leave.decl_type is DeclType.CONSTANT:
      raise SmvUnsupported("constant local")
    if enter.typ.kind == "struct":
      if enter.dimensions:
        raise SmvUnsupported("local array of structs")
      return self._local_struct(s, env, depth)
    if enter.dimensions:
      # `local int t[2] = a` parses and validates, but PyJanus cannot run it —
      # the interpreter raises a bare `TypeError`.  With no reference behaviour
      # to match, a model would be an authority on a program the implementation
      # cannot execute.
      raise SmvUnsupported("local array")
    if enter.typ.kind == "stack":
      # `local stack t = nil ... delocal stack t = nil`: the corpus uses this
      # in `reverse`.  The entry creates an empty stack and the exit demands it
      # be empty again -- a run-time obligation, like every other `delocal`,
      # and the same one PyJanus enforces.
      if leave.typ.kind != "stack":
        self._unconditional_error()
        return
      st = self._declare_stack(enter.ident.name)
      inner = dict(env)
      inner[enter.ident.name] = st
      self._stmts(s.body, inner, depth)
      self._check([f"{self._val(st.count)} = 0"])
      return
    if enter.typ.kind != "int":
      raise SmvUnsupported("non-scalar local")
    if leave.typ.kind != "int" or leave.dimensions:
      self._unconditional_error()
      return
    obl: list[str] = []
    init = self._iexpr(enter.init_expr, env, obl) if enter.init_expr is not None else "0"
    self._check(obl)
    # `--init zero` is "the store PyJanus actually starts from", so a local
    # belongs in it too.  Leaving it free made the zero store a *family* of
    # states rather than one, which over-approximates: every undecided program
    # in the corpus carried free locals.  The value is irrelevant to the
    # semantics — the `local` entry overwrites it before any read — so pinning
    # it removes states that differ only in a dead component.
    name = self._declare(enter.ident.name,
                         "0" if self.init_mode == "zero" else None)
    self.pending[name] = init

    inner = dict(env)
    inner[enter.ident.name] = name
    self._stmts(s.body, inner, depth)

    obl2: list[str] = []
    final = self._iexpr(leave.init_expr, inner, obl2) if leave.init_expr is not None else "0"
    self._check(obl2 + [f"{self._val(name)} = {final}"])

  def _struct_cells(self, entry: dict) -> list[str]:
    """Every SMV variable of an expanded struct, in declaration order."""
    cells: list[str] = []
    for value in entry.values():
      cells.extend(value if isinstance(value, tuple) else (value,))
    return cells

  def _struct_source(self, expr, env: _Env, who: str) -> list[str]:
    """Field values of a struct-valued expression, flattened in field order.

    Two forms occur: a plain struct variable, and an **element** of an array of
    structs (`out[j]`).  The second reads one cell per field, at the folded
    index, which is why the field-major layout pays off again — the index is the
    same for every field.  A variable index brings its own bounds obligation.
    """
    if not isinstance(expr, LvalExpr):
      raise SmvUnsupported(f"struct local initializer is not an l-value: {who}")
    lval = expr.lval
    entry = self._lookup(lval.ident.name, env)
    if not isinstance(entry, dict):
      raise SmvUnsupported(f"struct local initialized from a non-struct: {who}")
    if any(isinstance(sel, LvalField) for sel in lval.selectors):
      raise SmvUnsupported(f"struct local initialized from a field: {who}")
    if not lval.selectors:
      return [self._val(cell) for cell in self._struct_cells(entry)]
    obl: list[str] = []
    terms: list[str] = []
    for cells in entry.values():
      if not isinstance(cells, tuple):
        raise SmvUnsupported(f"indexing a scalar struct field: {who}")
      idx = self._flat_index(cells, lval.selectors, env, obl)
      terms.append(self._val(cells[int(idx)]) if idx.isdigit()
                   else self._read_at(cells, idx))
    self._check(obl)
    return terms

  def _local_struct(self, s: LocalStmt, env: _Env, depth: int) -> None:
    """`local struct Box e = a … delocal struct Box e = a` — a copy, checked back.

    Every field is bound on entry and compared again on exit, and the exit
    expression is re-evaluated **after** the body: PyJanus rejects both a body
    that moves the local and one that moves the source.
    """
    enter, leave = s.enter_decl, s.exit_decl
    if (leave.typ.kind != "struct" or leave.typ.name != enter.typ.name
        or leave.dimensions):
      self._unconditional_error()
      return
    if enter.init_expr is None or leave.init_expr is None:
      raise SmvUnsupported(f"struct local without an initializer: {enter.ident.name}")
    src = self._struct_source(enter.init_expr, env, enter.ident.name)
    fresh = self._declare_struct(enter, env, allow_init=True)
    dst_cells = self._struct_cells(fresh)
    if len(src) != len(dst_cells):
      raise SmvUnsupported(f"struct local of a different shape: {enter.ident.name}")
    for dst, term in zip(dst_cells, src):
      self.pending[dst] = term

    inner = dict(env)
    inner[enter.ident.name] = fresh
    self._stmts(s.body, inner, depth)

    # Re-read after the body, in the caller's terms: PyJanus evaluates the
    # `delocal` expression then, so a body that moves the source — or the index
    # that selects it — is rejected.
    back = self._struct_source(leave.init_expr, inner, enter.ident.name)
    if len(back) != len(dst_cells):
      raise SmvUnsupported(f"struct delocal of a different shape: {enter.ident.name}")
    self._check([f"{self._val(dst)} = {term}"
                 for dst, term in zip(dst_cells, back)])

  def _call(self, s, env: dict[str, str], depth: int, invert: bool) -> None:
    if s.external:
      raise SmvUnsupported("external call")
    proc = self.procs.get(s.ident.name)
    if proc is None:
      raise SmvUnsupported(f"undefined procedure: {s.ident.name}")
    if depth >= self.max_depth:
      # Leave for BOUND and drop this path: the pending updates are not carried
      # (BOUND is absorbing and only its *reachability* is asserted) and the
      # continuation goes to a fresh location nothing enters.  So an ERR proof
      # covers only the runs that stay below the bound; `INVARSPEC pc != BOUND`
      # is what turns it into an unconditional one.
      self.uses_bound = True
      self.trans.append(_Trans(self.loc, self._conj(self.path), (), BOUND_LOC))
      self._enter(self._loc())
      return
    inner: _Env = {}
    #: `(param, expr)` for every argument that is not an l-value.  These are
    #: *value arguments*: `runtime._bind_args` desugars `call f(n-1, r)` into
    #: `local t = n-1; call f(t, r); delocal t = n-1`, so the cell is writable
    #: and the obligation lands on return — the expression has to read back the
    #: value it was bound to.  Modelling them as read-only constants would
    #: reject callees that legitimately move the value and put it back.
    value_args: list[tuple] = []
    for param, arg in zip(proc.params, s.args):
      if param.typ.kind == "struct":
        if not isinstance(arg, LvalExpr) or arg.lval.selectors:
          raise SmvUnsupported("argument is not a plain variable")
        resolved = self._lookup(arg.lval.ident.name, env)
        if not isinstance(resolved, dict):
          raise SmvUnsupported(
              f"argument does not match the parameter's shape: {param.ident.name}")
        # By reference, exactly as for arrays: the same field entries, so a
        # write inside the callee updates the caller's struct.  This also makes
        # a formal passed onward to a third procedure resolve correctly.
        inner[param.ident.name] = resolved
        continue
      if param.typ.kind == "stack":
        # By reference, measured (§19): `call fill(s)` leaves the pushes in the
        # caller's `s`.  Binding the formal to the same `_Stack` -- same cells,
        # same count -- is exactly that.  Two formals landing on one stack is
        # allowed in Janus (also measured), so nothing is flagged here.
        if not isinstance(arg, LvalExpr) or arg.lval.selectors:
          raise SmvUnsupported("stack argument is not a plain variable")
        if not isinstance(env.get(arg.lval.ident.name), _Stack):
          # A non-stack passed to a stack formal: PyJanus raises when it reaches
          # the call ("Couldn't match expected type"), so reaching it is the
          # error.
          self._unconditional_error()
          return
        inner[param.ident.name] = self._stack_of(arg.lval.ident.name, env)
        continue
      if param.typ.kind != "int":
        raise SmvUnsupported("non-scalar parameter")
      if isinstance(arg, LvalExpr) and not arg.lval.selectors \
          and isinstance(env.get(arg.lval.ident.name), _Stack):
        # A stack passed where an `int` is expected.  PyJanus raises on reaching
        # the call, so this is an unconditional ERR edge -- NOT a silent bind.
        # Found by `type-error-argument.ja`, which this encoding first *proved*
        # safe: the shape check below compares against `tuple` and a stack is
        # not one, so the mismatch slipped through it.
        self._unconditional_error()
        return
      if not isinstance(arg, LvalExpr):
        value_args.append((param, arg))
        continue
      if arg.lval.selectors:
        # A cell or a field passed by reference.  Janus passes the CELL, so
        # binding the formal to that element's variable makes a write inside the
        # callee update the caller's array — the same "one entity, two names"
        # the plain-variable case relies on, and the same aliasing checks apply
        # to it (two formals may still land on one element; the per-statement
        # checks below decide that, not this binding).
        #
        # Only a constant index names one element. A variable index picks its
        # cell at run time, so there is no single variable to bind and it stays
        # refused rather than guessed.
        try:
          inner[param.ident.name] = self._lval_name(arg.lval, env)
        except SmvUnsupported:
          raise SmvUnsupported("argument is not a plain variable") from None
        continue
      # Two formals may resolve to one variable.  That is not itself an error:
      # PyJanus checks each statement as it reaches it, so a body that never
      # brings them together runs fine, and rejecting the call outright would
      # be a false alarm.  The per-statement checks in `_assign` and the swap
      # case above catch the bodies that do bring them together.
      resolved = self._lookup(arg.lval.ident.name, env)
      # An unspecified length `int a[]` needs nothing new: inlining has the
      # actual in hand, arrays are by reference in Janus, and binding the formal
      # to the *same* tuple of element variables makes a write inside the callee
      # update the caller's array.  The length travels with the tuple, so the
      # same procedure inlined against two arrays expands to two sizes.
      if bool(param.dimensions) != isinstance(resolved, tuple):
        raise SmvUnsupported(
            f"argument does not match the parameter's shape: {param.ident.name}")
      if param.dimensions:
        shape = self._shape(resolved)
        if len(param.dimensions) != len(shape):
          # Refuse rather than answer: the formal and the actual disagree about
          # the rank, so no index in the body would mean what it says.
          raise SmvUnsupported(
              f"parameter of rank {len(param.dimensions)} bound to an array of "
              f"rank {len(shape)}: {param.ident.name}")
        for declared, extent in zip(param.dimensions, shape):
          if isinstance(declared, Number) and declared.value != extent:
            # A parameter may state its length, and PyJanus checks it *at the
            # call* ("Expecting array of size [3] but got size [4]"), so
            # reaching the call is the error.  Without this the model proved
            # such a program safe.
            return self._unconditional_error()
      inner[param.ident.name] = resolved
    for param, arg in value_args:
      if param.dimensions or param.decl_type is DeclType.CONSTANT:
        # An array cannot be written as an expression, and a `const` parameter
        # binds through `ConstantParamProxy` (read-only) instead.  Neither is
        # this desugaring, so neither is answered here.
        raise SmvUnsupported(f"value argument to a non-plain parameter: {param.ident.name}")
      obl: list[str] = []
      bound = self._iexpr(arg, env, obl)
      self._check(obl)
      name = self._declare(param.ident.name,
                           "0" if self.init_mode == "zero" else None)
      self.pending[name] = bound
      inner[param.ident.name] = name
    body = invert_stmts(proc.body, False) if invert else proc.body
    self._stmts(body, inner, depth + 1)
    for param, arg in value_args:
      # Re-evaluated **after** the body and in the *caller's* environment: a
      # callee that moves `m` through another parameter changes what `m + 1`
      # means on return, and PyJanus rejects exactly that.
      obl: list[str] = []
      restored = self._iexpr(arg, env, obl)
      self._check(obl + [f"{self._val(inner[param.ident.name])} = {restored}"])

  # -- driver ----------------------------------------------------------

  def _declare_array(self, decl, env: _Env) -> tuple[str, ...]:
    """One SMV variable per element, named `a_0`, `a_1`, ...

    `_uniq` deduplicates, so a source variable that happens to be called `a_0`
    does not collide.  Every dimension must be a constant: an unspecified length
    needs the call site to supply it.
    """
    shape = self._constant_shape(decl.dimensions, decl.ident.name)
    size = 1
    for extent in shape:
      size *= extent
    if decl.init_expr is None:
      inits: list[str | None] = [("0" if self.init_mode == "zero" else None)] * size
    elif isinstance(decl.init_expr, ArrayExpr):
      if len(decl.init_expr.items) != size:
        raise SmvUnsupported(f"array initializer length mismatch: {decl.ident.name}")
      obl: list[str] = []
      inits = [self._iexpr(item, env, obl) for item in decl.init_expr.items]
      if obl:
        raise SmvUnsupported("division in a declaration initializer")
    else:
      raise SmvUnsupported(f"array initializer outside the fragment: {decl.ident.name}")
    return self._expand_array(decl.ident.name, shape, inits)

  def _constant_shape(self, dimensions, who: str) -> tuple[int, ...]:
    """Every dimension as a positive constant, or refuse."""
    shape = []
    total = 1
    for dim in dimensions:
      if not isinstance(dim, Number):
        raise SmvUnsupported(f"array of unspecified length: {who}")
      if dim.value < 1:
        # PyJanus rejects the declaration outright ("Array size must be greater
        # than or equal to one"), so the program never runs.  Emitting a model
        # anyway would prove a program safe that cannot even start.
        raise SmvUnsupported(f"array size must be at least one: {who}[{dim.value}]")
      shape.append(dim.value)
      total *= dim.value
    if total > _MAX_ARRAY:
      raise SmvUnsupported(f"array too large to expand: {who}[{total}]")
    return tuple(shape)

  def _suffixes(self, shape: tuple[int, ...]) -> list[str]:
    """`_0_1`-style name suffixes, row-major, matching the flat cell order."""
    out = [""]
    for extent in shape:
      out = [f"{prefix}_{i}" for prefix in out for i in range(extent)]
    return out

  def _expand_array(self, base_name: str, shape: tuple[int, ...],
                    inits: list) -> tuple[str, ...]:
    """One cell per element of `shape`, flat and row-major.

    Shared by a top-level array declaration and by an array *field* of a struct,
    which differ only in the name they hang off.  The shape is registered so
    that indexing can fold it back; the cells themselves stay one flat tuple, so
    everything downstream of the fold is rank-agnostic.
    """
    size = len(inits)
    if self.arrays_mode == "native":
      # nuXmv has its own array type, and a *read* at a variable index is
      # allowed on it (`a[i]`), which is what removes the case that copies every
      # element's pending term.  A *write* at a variable index is not
      # ("Expressions not allowed in array subscripts on left hand side of
      # assignments"), so the per-element conditional update stays.
      base = self._uniq(base_name)
      self.array_bases.add(base)
      self.array_decls.append((base, size))
      cells = tuple(f"{base}[{i}]" for i in range(size))
      for i, cell in enumerate(cells):
        self.varnames.append(cell)
        self.var_init[cell] = inits[i]
        self.array_of[cell] = base
    else:
      cells = tuple(self._declare(f"{base_name}{suffix}", inits[i])
                    for i, suffix in enumerate(self._suffixes(shape)))
    if len(shape) != 1:
      self.dims[cells] = shape
    return cells

  def _declare_struct(self, decl, env: _Env, allow_init: bool = False) -> dict:
    """One SMV variable per field.

    A field is itself a scalar or an array, and no field has a struct type in
    this dialect's corpus, so the expansion bottoms out here.  Array fields are
    a later step; they are refused rather than half-translated.
    """
    sdef = self.structs.get(decl.typ.name)
    if sdef is None:
      raise SmvUnsupported(f"unknown struct type: {decl.typ.name}")
    if decl.init_expr is not None and not allow_init:
      # A `local` supplies one and copies it in field by field (`_local_struct`);
      # a top-level declaration has nothing to copy from.
      raise SmvUnsupported(f"struct initializer: {decl.ident.name}")
    outer = self._constant_shape(decl.dimensions, decl.ident.name)
    out: dict = {}
    for field in sdef.fields:
      if field.typ.kind != "int":
        raise SmvUnsupported(f"non-int struct field: {decl.typ.name}.{field.ident.name}")
      init = "0" if self.init_mode == "zero" else None
      name = f"{decl.ident.name}_{field.ident.name}"
      inner = self._constant_shape(field.dimensions,
                                   f"{decl.typ.name}.{field.ident.name}")
      # Field-major: one array per field, `p_x[0]` / `p_x[1]`.  The native
      # encoding needs it that way (an array variable per field), and it keeps
      # the name the same as a plain struct's field.
      #
      # The two shapes simply concatenate.  `g[i].v[j]` puts the field selector
      # *between* the indices, and `_base_of` lifts it out, so what reaches the
      # fold is `[i, j]` against the shape `outer ++ inner` — row-major, element
      # before field-element.  A field that is itself an array of a scalar
      # struct field needs nothing special for the same reason.
      shape = outer + inner
      if not shape:
        out[field.ident.name] = self._declare(name, init)
        continue
      size = 1
      for extent in shape:
        size *= extent
      if size > _MAX_ARRAY:
        raise SmvUnsupported(f"array too large to expand: {name}[{size}]")
      out[field.ident.name] = self._expand_array(name, shape, [init] * size)
    return out

  def _declare_stack(self, base_name: str) -> _Stack:
    """`depth` cells and a count, both starting empty.

    The count is the only thing that decides which cells are live, so the cells
    themselves start at 0 in either init mode: under `--init any` an arbitrary
    cell above the count is unobservable, and an arbitrary count would model
    initial states the language cannot produce (a stack is created empty).
    """
    cells = self._expand_array(base_name, (_STACK_DEPTH,), [0] * _STACK_DEPTH)
    count = self._declare(f"{base_name}_n", "0")
    return _Stack(cells, count, _STACK_DEPTH)

  def _stack_of(self, name: str, env: _Env) -> _Stack:
    entry = env.get(name)
    if not isinstance(entry, _Stack):
      raise SmvUnsupported(f"not a stack: {name}")
    return entry

  def _push(self, s, env: _Env) -> None:
    """`push(x, st)`: the value moves onto the stack and `x` is left 0.

    Measured, not assumed (§19): the source is cleared, which is what makes the
    statement injective and `pop` its inverse.  A push into a full model leaves
    for BOUND rather than ERR — the program is fine, the model simply stops
    following it.
    """
    if not isinstance(env.get(s.ident.name), _Stack):
      return self._unconditional_error()   # `push(x, notastack)` is a type error
    st = self._stack_of(s.ident.name, env)
    if not isinstance(s.expr, LvalExpr):
      raise SmvUnsupported("push of a non-variable")
    src = self._lval_name(s.expr.lval, env)
    obl: list[str] = []
    value = self._val(src)
    idx = self._val(st.count)

    # Full: leave for BOUND and drop the path, exactly as `_call` does at
    # max_depth.  Not ERR: overflowing the model is not the program failing.
    self.uses_bound = True
    self.trans.append(_Trans(self.loc, self._conj(self.path + [f"{idx} >= {st.depth}"]),
                             (), BOUND_LOC))
    self.path.append(f"{idx} < {st.depth}")

    before = [self._val(name) for name in st.cells]
    for k, name in enumerate(st.cells):
      self.pending[name] = f"(case {idx} = {k} : {value}; TRUE : {before[k]}; esac)"
    self.pending[st.count] = f"({idx} + 1)"
    self.pending[src] = "0"
    self._check(obl)
    self._seal()

  def _pop(self, s, env: _Env) -> None:
    """`pop(x, st)`: two run-time obligations, both measured (§19).

    `Can't pop from empty stack` and `Can't pop to non-zero variable` are
    ordinary Janus runtime errors, so they are ERR edges — the same kind as an
    assertion failure, and deliberately not the BOUND edge that `push` uses.
    """
    if not isinstance(env.get(s.ident.name), _Stack):
      return self._unconditional_error()   # `pop(x, notastack)` is a type error
    st = self._stack_of(s.ident.name, env)
    if not isinstance(s.expr, LvalExpr):
      raise SmvUnsupported("pop into a non-variable")
    dst = self._lval_name(s.expr.lval, env)
    idx = f"({self._val(st.count)} - 1)"
    self._check([f"{self._val(st.count)} > 0", f"{self._val(dst)} = 0"])
    top = self._read_at(st.cells, idx)
    before = [self._val(name) for name in st.cells]
    self.pending[dst] = top
    for k, name in enumerate(st.cells):
      self.pending[name] = f"(case {idx} = {k} : 0; TRUE : {before[k]}; esac)"
    self.pending[st.count] = f"({self._val(st.count)} - 1)"
    self._seal()

  def run(self) -> str:
    main = self.program.main
    assert main is not None
    env: _Env = {}
    for decl in main.vdecls:
      if decl.typ.kind == "struct":
        env[decl.ident.name] = self._declare_struct(decl, env)
        continue
      if decl.typ.kind == "stack":
        env[decl.ident.name] = self._declare_stack(decl.ident.name)
        continue
      if decl.typ.kind != "int":
        # Name the KIND, not just the variable: a blocker census cannot tell a
        # stack from a bool from the variable's name, and "non-scalar" was
        # covering both while the coverage notes read it as "stack".
        raise SmvUnsupported(
            f"non-scalar declaration ({decl.typ.kind}): {decl.ident.name}")
      if decl.dimensions:
        env[decl.ident.name] = self._declare_array(decl, env)
        continue
      if decl.init_expr is not None:
        obl: list[str] = []
        init = self._iexpr(decl.init_expr, env, obl)
        if obl:
          raise SmvUnsupported("division in a declaration initializer")
      else:
        init = "0" if self.init_mode == "zero" else None
      env[decl.ident.name] = self._declare(decl.ident.name, init)
    entry = self.loc
    self._stmts(main.stmts, env, 0)
    final = self._seal()
    return self._render(entry, final)

  def _guard_of(self, t: _Trans) -> str:
    return f"pc = {t.src}" if t.guard == "TRUE" else f"pc = {t.src} & {t.guard}"

  def _render(self, entry: int, final: int) -> str:
    if self.style == "trans":
      # The relational form needs an explicit self-loop everywhere, or nuXmv
      # reports a deadlock; the functional form gets it from the `TRUE` default.
      live = {t.src for t in self.trans}
      for loc in range(_FIRST_LOC, self._next_loc):
        if loc not in live:
          self.trans.append(_Trans(loc, "TRUE", (), loc))
      if self.uses_err:
        self.trans.append(_Trans(ERR_LOC, "TRUE", (), ERR_LOC))
      if self.uses_bound:
        self.trans.append(_Trans(BOUND_LOC, "TRUE", (), BOUND_LOC))

    lines = ["MODULE main", "VAR", f"  pc : {ERR_LOC}..{self._next_loc - 1};"]
    for base, size in self.array_decls:
      lines.append(f"  {base} : array 0..{size - 1} of integer;")
    for name in self.varnames:
      if name not in self.array_of:
        lines.append(f"  {name} : integer;")
    lines.append("")
    lines.append(f"-- pc = {ERR_LOC} : a Janus runtime assertion failed (ERR)")
    if self.uses_bound:
      lines.append(f"-- pc = {BOUND_LOC} : the inlining bound was hit (BOUND) —"
                   " an ERR proof then covers only the runs that stay below it")
    lines.append(f"-- pc = {entry} : entry,  pc = {final} : normal termination")
    lines.append("")
    if self.defines:
      lines.append("DEFINE")
      for name, body in self.defines:
        lines.append(f"  {name} := {body};")
      lines.append("")
    if self.style == "trans":
      init_parts = [f"pc = {entry}"]
      for name in self.varnames:
        value = self.var_init[name]
        if value is not None:
          init_parts.append(f"{name} = {value}")
      if self.assume:
        init_parts.append(f"({self.assume})")
      lines.append("INIT")
      lines.append("  " + " & ".join(init_parts) + ";")
      lines.append("")
      lines.append("TRANS")
      rendered = []
      for t in self.trans:
        updated = dict(t.updates)
        parts = [f"pc = {t.src}"]
        if t.guard != "TRUE":
          parts.append(t.guard)
        parts.append(f"next(pc) = {t.dst}")
        for name in self.varnames:
          parts.append(f"next({name}) = {updated.get(name, name)}")
        rendered.append("  (" + " & ".join(parts) + ")")
      lines.append(" |\n".join(rendered) + ";")
      lines.append("")
    else:
      # Functional form: one next-state function per variable.  The `TRUE`
      # default absorbs every frame condition, so the model shrinks from
      # |vars| x |edges| equalities to roughly |edges| case branches, and the
      # system is deterministic by construction rather than by derivation.
      lines.append("ASSIGN")
      lines.append(f"  init(pc) := {entry};")
      for name in self.varnames:
        value = self.var_init[name]
        if value is not None:
          lines.append(f"  init({name}) := {value};")
      lines.append("  next(pc) := case")
      for t in self.trans:
        lines.append(f"      {self._guard_of(t)} : {t.dst};")
      lines.append("      TRUE : pc;")
      lines.append("    esac;")
      for name in self.varnames:
        writes = [(t, dict(t.updates)[name]) for t in self.trans
                  if any(n == name for n, _ in t.updates)]
        if not writes:
          # A variable with no `next` at all is **unconstrained** in SMV, not
          # frozen: it may take any value at every step.  A read-only variable
          # would then wander, refuting programs that run.  (The relational form
          # is immune, since it restates `next(v) = v` on every edge.)
          lines.append(f"  next({name}) := {name};")
          continue
        lines.append(f"  next({name}) := case")
        for t, update in writes:
          lines.append(f"      {self._guard_of(t)} : {update};")
        lines.append(f"      TRUE : {name};")
        lines.append("    esac;")
      lines.append("")
      if self.assume:
        lines.append(f"INIT {self.assume};")
        lines.append("")
    lines.append(f"INVARSPEC pc != {ERR_LOC}")
    if self.uses_bound:
      lines.append(f"INVARSPEC pc != {BOUND_LOC}")
    return "\n".join(lines) + "\n"


def compile_to_smv(program: Program, *, init: str = "any", assume: str | None = None,
                   max_depth: int = 16, style: str = "assign",
                   arrays: str = "native",
                   mod_bits: int | str | None = None,
                   mod_prime: int | str | None = None) -> str:
  """Compile `program` to an nuXmv model asserting that no assertion can fail.

  `init` is `"any"` (variables unconstrained — proves totality on the whole
  domain) or `"zero"` (the store PyJanus actually starts from).  `assume` is an
  SMV boolean expression restricting the initial store, i.e. a precondition.
  `max_depth` bounds procedure inlining.  A run that reaches the bound leaves for
  the `BOUND` location and its continuation is dropped, so proving `pc != ERR`
  is a statement about *the runs that stay below the bound* — not "correct up to
  depth n".  Proving `pc != BOUND` as well says no run reaches it, which makes
  the ERR proof unconditional.
  `style` selects the relational (`"trans"`) or functional (`"assign"`) shape.
  `arrays` selects how an array is carried: `"native"` (default) uses nuXmv's own
  `array 0..n-1 of integer`, so a read at a variable index is one term; `"expand"`
  gives every element its own integer variable and reads become a `case` over
  them.  The two decide the same programs (measured on the corpus), but `expand`
  grows super-linearly in the array length while `native` grows linearly.
  """
  if mod_bits not in (None, "") or mod_prime not in (None, ""):
    # The modular modes change what *every* operation computes, and this
    # back-end compiles the unbounded-integer semantics.  Emitting a model
    # anyway would prove `INVARSPEC pc != ERR` of a different program: under
    # `-m 8` the interpreter wraps `100 += 100` to -56 and fails an assertion
    # the unbounded model satisfies.  Refusing here rather than only in the CLI
    # keeps library callers (verify_corpus.py, the tests) fail-closed too.
    raise SmvUnsupported(
        "the modular modes (-m BITS / -p PRIME) are outside this back-end: "
        "they wrap every value, while the emitted model is over unbounded "
        "integers, so a proof about it would be about a different program")
  if init not in ("any", "zero"):
    raise ValueError(f"init must be 'any' or 'zero', not {init!r}")
  if style not in ("trans", "assign"):
    raise ValueError(f"style must be 'trans' or 'assign', not {style!r}")
  if arrays not in ("expand", "native"):
    raise ValueError(f"arrays must be 'expand' or 'native', not {arrays!r}")
  return _Compiler(program, init, assume, max_depth, style, arrays).run()


def collect_unsupported(program: Program, **kwargs) -> list[str]:
  """Every reason `program` is outside the fragment, not just the first.

  Diagnostic only: **the compiled model is discarded**, because skipping a
  rejected statement leaves the compiler's state inconsistent.  Use this to
  size a feature before implementing it — `compile_to_smv` reports the first
  blocker, and a tally of first blockers is not an upper bound on how many
  programs a feature would admit.

  Reasons after the first can be *fallout* from a skipped statement (a variable
  the skipped declaration never bound now reads as "out of the fragment").
  The caller has to allow for that; `tools/blockers.py` marks such reasons.
  """
  global _COLLECT
  if _COLLECT is not None:
    raise RuntimeError("collect_unsupported is not re-entrant")
  reasons: list[str] = []
  _COLLECT = reasons
  try:
    compile_to_smv(program, **kwargs)
  except SmvUnsupported as exc:
    # Raised outside `_stmts` (whole-program refusals: no main, modular mode).
    reasons.append(str(exc))
  finally:
    _COLLECT = None
  return reasons
