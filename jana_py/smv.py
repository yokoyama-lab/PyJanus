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
from .ast import LocalStmt
from .ast import ArrayExpr
from .ast import LvalExpr
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

#: A source name resolves either to one SMV variable (a scalar) or, for an
#: expanded array, to the tuple of its elements' variables.
_Env = dict  # dict[str, str | tuple[str, ...]]

#: Reserved in SMV (plus `pc`, which names the program counter).  A Janus
#: variable with one of these names is renamed, the way `c_codegen.py` renames
#: identifiers that collide with C++ keywords.
_SMV_RESERVED = frozenset({
    "pc", "MODULE", "VAR", "IVAR", "FROZENVAR", "DEFINE", "ASSIGN", "INIT",
    "TRANS", "INVAR", "INVARSPEC", "CTLSPEC", "LTLSPEC", "SPEC", "FAIRNESS",
    "JUSTICE", "COMPASSION", "CONSTANTS", "case", "esac", "init", "next",
    "self", "TRUE", "FALSE", "boolean", "integer", "real", "word", "array",
    "of", "in", "union", "xor", "xnor", "mod", "process", "abs", "max", "min",
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


@dataclass(frozen=True)
class _Trans:
  src: int
  guard: str
  updates: tuple[tuple[str, str], ...]
  dst: int


class _Compiler:
  def __init__(self, program: Program, init: str, assume: str | None, max_depth: int,
               style: str = "trans"):
    if program.main is None:
      raise SmvUnsupported("no main procedure")
    self.program = program
    self.procs = {p.procname.name: p for p in program.procs}
    self.init_mode = init
    self.assume = assume
    self.max_depth = max_depth
    self.style = style
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
    while name in self.varnames:
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
    entry = self._lookup(lval.ident.name, env)
    if not lval.selectors:
      if isinstance(entry, tuple):
        raise SmvUnsupported(f"whole-array l-value: {lval.ident.name}")
      return entry == name
    if not isinstance(entry, tuple):
      raise SmvUnsupported(f"indexing a non-array: {lval.ident.name}")
    if len(lval.selectors) != 1 or not isinstance(lval.selectors[0], LvalIndex):
      raise SmvUnsupported("struct field or multi-dimensional l-value")
    index = lval.selectors[0].expr
    if isinstance(index, Number):
      return 0 <= index.value < len(entry) and entry[index.value] == name
    if name in entry:
      raise SmvUnsupported(
          "aliasing between a cell and a variable index of the same array")
    return self._occurs(name, index, env)

  def _lookup(self, name: str, env: dict[str, str]) -> str:
    if name not in env:
      raise SmvUnsupported(f"variable out of the fragment: {name}")
    return env[name]

  def _lval_name(self, lval, env: _Env) -> str:
    """The SMV variable an l-value denotes.

    A scalar denotes its own variable; an expanded array denotes one element,
    named by a **constant** index.  A variable index needs a `case` over the
    elements and is not translated yet.
    """
    entry = self._lookup(lval.ident.name, env)
    if not lval.selectors:
      if isinstance(entry, tuple):
        raise SmvUnsupported(f"whole-array l-value: {lval.ident.name}")
      return entry
    if not isinstance(entry, tuple):
      raise SmvUnsupported(f"indexing a non-array: {lval.ident.name}")
    if len(lval.selectors) != 1 or not isinstance(lval.selectors[0], LvalIndex):
      raise SmvUnsupported("struct field or multi-dimensional l-value")
    index = lval.selectors[0].expr
    if not isinstance(index, Number):
      raise SmvUnsupported("variable array index")
    if not 0 <= index.value < len(entry):
      # The caller checks bounds first, so this is defensive only.
      raise SmvUnsupported(f"index out of bounds: {lval.ident.name}[{index.value}]")
    return entry[index.value]

  def _oob_lval(self, lval, env: _Env) -> bool:
    """Is this a *constant* index outside its array?

    PyJanus raises "Array index `[5]' was out of bounds" when it reaches such a
    statement, so reaching it is the error.  A variable index is not decided
    here — it is refused by `_lval_name` until the `case` encoding exists.
    """
    entry = env.get(lval.ident.name)
    if not isinstance(entry, tuple) or not lval.selectors:
      return False
    selector = lval.selectors[0]
    if not isinstance(selector, LvalIndex):
      return False
    if not isinstance(selector.expr, Number):
      return self._oob(selector.expr, env)   # a nested constant index may still be
    return not 0 <= selector.expr.value < len(entry)

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
    entry = self._lookup(lval.ident.name, env)
    if not lval.selectors:
      if isinstance(entry, tuple):
        raise SmvUnsupported(f"whole-array l-value: {lval.ident.name}")
      return self._val(entry)
    if not isinstance(entry, tuple):
      raise SmvUnsupported(f"indexing a non-array: {lval.ident.name}")
    if len(lval.selectors) != 1 or not isinstance(lval.selectors[0], LvalIndex):
      raise SmvUnsupported("struct field or multi-dimensional l-value")
    index = lval.selectors[0].expr
    if isinstance(index, Number):
      if not 0 <= index.value < len(entry):
        raise SmvUnsupported(f"index out of bounds: {lval.ident.name}[{index.value}]")
      return self._val(entry[index.value])
    idx = self._dynamic_index(index, env, obl, len(entry))
    return self._read_at(entry, idx)

  def _dynamic_index(self, index, env: _Env, obl: list[str], size: int) -> str:
    """Translate a variable index and check its range into ERR."""
    idx = self._iexpr(index, env, obl)
    obl.append(f"({idx}) >= 0")
    obl.append(f"({idx}) < {size}")
    return idx

  def _read_at(self, entry: tuple, idx: str) -> str:
    """The value of the selected element, as a `case` over the pending map."""
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
      self._stmt(stmt, env, depth)

  def _stmt(self, s, env: dict[str, str], depth: int) -> None:
    if isinstance(s, SkipStmt):
      return
    if isinstance(s, PrintsStmt):
      if s.prints.reversible:
        raise SmvUnsupported("reversible read/write")
      return  # printing does not touch the store
    if isinstance(s, AssignStmt):
      if self._oob_lval(s.lval, env) or self._oob(s.expr, env):
        return self._unconditional_error()
      return self._assign(s, env)
    if isinstance(s, SwapStmt):
      if self._oob_lval(s.left, env) or self._oob_lval(s.right, env):
        return self._unconditional_error()
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
    if isinstance(s, AssertStmt):
      if self._oob(s.expr, env):
        return self._unconditional_error()
      self._check([self._cond(s.expr, env)])
      return
    if isinstance(s, IfStmt):
      return self._if(s, env, depth)
    if isinstance(s, FromStmt):
      return self._from(s, env, depth)
    if isinstance(s, LocalStmt):
      return self._local(s, env, depth)
    if isinstance(s, (CallStmt, UncallStmt)):
      return self._call(s, env, depth, isinstance(s, UncallStmt))
    raise SmvUnsupported(f"statement outside the fragment: {type(s).__name__}")

  def _assign(self, s: AssignStmt, env: _Env) -> None:
    entry = self._lookup(s.lval.ident.name, env)
    if (isinstance(entry, tuple) and len(s.lval.selectors) == 1
        and isinstance(s.lval.selectors[0], LvalIndex)
        and not isinstance(s.lval.selectors[0].expr, Number)):
      return self._assign_dynamic(s, env, entry)
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

  def _assign_dynamic(self, s: AssignStmt, env: _Env, entry: tuple) -> None:
    """`a[i] op= e`: every element is updated conditionally on the index.

    The operator's obligations are computed **once, on the value read at `i`** —
    not per element.  Only the selected element is written, so a per-element
    divisibility obligation would fire for elements the statement never touches:
    a false alarm of exactly the kind the call-site double-binding check used to
    produce.
    """
    for element in entry:
      if self._occurs(element, s.expr, env) or \
         self._occurs(element, s.lval.selectors[0].expr, env):
        raise SmvUnsupported(
            "aliasing between a variable index and the same array")
    obl: list[str] = []
    rhs = self._iexpr(s.expr, env, obl)
    idx = self._dynamic_index(s.lval.selectors[0].expr, env, obl, len(entry))
    new = self._apply(s.mod_op, self._read_at(entry, idx), rhs, obl)
    self._check(obl)
    before = [self._val(name) for name in entry]   # read every element first
    for k, name in enumerate(entry):
      self.pending[name] = f"(case {idx} = {k} : {new}; TRUE : {before[k]}; esac)"
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

  def _local(self, s: LocalStmt, env: dict[str, str], depth: int) -> None:
    enter, leave = s.enter_decl, s.exit_decl
    for decl in (enter, leave):
      if decl.dimensions or decl.typ.kind != "int":
        raise SmvUnsupported("non-scalar local")
      if decl.decl_type is DeclType.CONSTANT:
        raise SmvUnsupported("constant local")
    if enter.ident.name != leave.ident.name:
      # Another run-time check: PyJanus raises when it reaches the `delocal`.
      self._unconditional_error()
      return
    obl: list[str] = []
    init = self._iexpr(enter.init_expr, env, obl) if enter.init_expr is not None else "0"
    self._check(obl)
    name = self._declare(enter.ident.name, None)
    self.pending[name] = init

    inner = dict(env)
    inner[enter.ident.name] = name
    self._stmts(s.body, inner, depth)

    obl2: list[str] = []
    final = self._iexpr(leave.init_expr, inner, obl2) if leave.init_expr is not None else "0"
    self._check(obl2 + [f"{self._val(name)} = {final}"])

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
    inner: dict[str, str] = {}
    for param, arg in zip(proc.params, s.args):
      if param.dimensions or param.typ.kind != "int":
        raise SmvUnsupported("non-scalar parameter")
      if not isinstance(arg, LvalExpr) or arg.lval.selectors:
        raise SmvUnsupported("argument is not a plain variable")
      # Two formals may resolve to one variable.  That is not itself an error:
      # PyJanus checks each statement as it reaches it, so a body that never
      # brings them together runs fine, and rejecting the call outright would
      # be a false alarm.  The per-statement checks in `_assign` and the swap
      # case above catch the bodies that do bring them together.
      resolved = self._lookup(arg.lval.ident.name, env)
      if isinstance(resolved, tuple):
        raise SmvUnsupported("array argument")
      inner[param.ident.name] = resolved
    body = invert_stmts(proc.body, False) if invert else proc.body
    self._stmts(body, inner, depth + 1)

  # -- driver ----------------------------------------------------------

  def _declare_array(self, decl, env: _Env) -> tuple[str, ...]:
    """One SMV variable per element, named `a_0`, `a_1`, ...

    `_uniq` deduplicates, so a source variable that happens to be called `a_0`
    does not collide.  Only a single constant dimension: an unspecified length
    needs the call site to supply it, and a second dimension needs an index fold.
    """
    if len(decl.dimensions) != 1:
      raise SmvUnsupported(f"multi-dimensional array: {decl.ident.name}")
    dim = decl.dimensions[0]
    if not isinstance(dim, Number):
      raise SmvUnsupported(f"array of unspecified length: {decl.ident.name}")
    size = dim.value
    if size < 1:
      # PyJanus rejects the declaration outright ("Array size must be greater
      # than or equal to one"), so the program never runs.  Emitting a model
      # anyway would prove a program safe that cannot even start.
      raise SmvUnsupported(f"array size must be at least one: {decl.ident.name}[{size}]")
    if size > _MAX_ARRAY:
      raise SmvUnsupported(f"array too large to expand: {decl.ident.name}[{size}]")
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
    return tuple(self._declare(f"{decl.ident.name}_{i}", inits[i]) for i in range(size))

  def run(self) -> str:
    main = self.program.main
    assert main is not None
    env: _Env = {}
    for decl in main.vdecls:
      if decl.typ.kind != "int":
        raise SmvUnsupported(f"non-scalar declaration: {decl.ident.name}")
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
    for name in self.varnames:
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
  return _Compiler(program, init, assume, max_depth, style).run()
