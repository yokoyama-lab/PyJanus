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

Two traps this encoding has to avoid, both of which a naive translation falls
into:

* **Integer division.**  nuXmv's `/` truncates toward zero, while Janus (like
  Python) floors, and nuXmv's `mod` is not available on integers at all inside
  the SMT engine.  Every division site is therefore emitted through the
  floor-division macro `_div_defines` builds, checked against the interpreter's
  semantics in `tests/verify/test_smv.py`.
* **Sort confusion.**  Janus comparisons yield integers, so `x += (y > 0)` is
  legal.  The translation is two-sorted and *refuses* such expressions rather
  than guessing — the same discipline `coq/RevLowerExpr.v` formalizes as `wf`.

Anything outside the fragment raises `SmvUnsupported`; nothing is ever emitted
as an approximation, because an unsound model would turn a proof into a lie.
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
from .ast import LvalExpr
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
  def __init__(self, program: Program, init: str, assume: str | None, max_depth: int):
    if program.main is None:
      raise SmvUnsupported("no main procedure")
    self.program = program
    self.procs = {p.procname.name: p for p in program.procs}
    self.init_mode = init
    self.assume = assume
    self.max_depth = max_depth
    self.varnames: list[str] = []
    self.var_init: dict[str, str | None] = {}
    self.defines: list[tuple[str, str]] = []
    self.trans: list[_Trans] = []
    self._next_loc = _FIRST_LOC
    self._uid = 0
    self.uses_err = False
    self.uses_bound = False

  # -- small helpers ---------------------------------------------------

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

  def _emit(self, src: int, guard: str, updates: tuple[tuple[str, str], ...], dst: int) -> None:
    self.trans.append(_Trans(src, guard, updates, dst))

  def _err(self, src: int, guard: str) -> None:
    self.uses_err = True
    self.trans.append(_Trans(src, guard, (), ERR_LOC))

  def _bound(self, src: int) -> None:
    self.uses_bound = True
    self.trans.append(_Trans(src, "TRUE", (), BOUND_LOC))

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
    """Does the SMV variable `name` occur in `e` after resolving through `env`?"""
    if isinstance(e, LvalExpr):
      return not e.lval.selectors and env.get(e.lval.ident.name) == name
    if isinstance(e, BinExpr):
      return self._occurs(name, e.left, env) or self._occurs(name, e.right, env)
    if isinstance(e, UnaryExpr):
      return self._occurs(name, e.expr, env)
    return False

  def _lookup(self, name: str, env: dict[str, str]) -> str:
    if name not in env:
      raise SmvUnsupported(f"variable out of the fragment: {name}")
    return env[name]

  def _lval_name(self, lval, env: dict[str, str]) -> str:
    if lval.selectors:
      raise SmvUnsupported("array/struct l-value")
    return self._lookup(lval.ident.name, env)

  def _iexpr(self, e, env: dict[str, str], obl: list[str]) -> str:
    """Translate an integer-sorted expression, appending safety obligations."""
    if isinstance(e, Number):
      return str(e.value) if e.value >= 0 else f"({e.value})"
    if isinstance(e, LvalExpr):
      return self._lval_name(e.lval, env)
    if isinstance(e, BinExpr):
      if e.op in _ARITH:
        left = self._iexpr(e.left, env, obl)
        right = self._iexpr(e.right, env, obl)
        return f"({left} {_ARITH[e.op]} {right})"
      if e.op in (BinOpKind.DIV, BinOpKind.MOD):
        left = self._iexpr(e.left, env, obl)
        right = self._iexpr(e.right, env, obl)
        obl.append(f"({right}) != 0")
        fq, fr = self._div_defines(left, right)
        return fq if e.op is BinOpKind.DIV else fr
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

  def _cond(self, e, env: dict[str, str]) -> tuple[str, str]:
    """A condition together with the guard under which evaluating it is safe."""
    obl: list[str] = []
    text = self._bexpr(e, env, obl)
    return text, self._conj(obl)

  # -- statements ------------------------------------------------------

  def _stmts(self, stmts, env: dict[str, str], loc: int, depth: int) -> int:
    for stmt in stmts:
      loc = self._stmt(stmt, env, loc, depth)
    return loc

  def _stmt(self, s, env: dict[str, str], loc: int, depth: int) -> int:
    if isinstance(s, SkipStmt):
      return loc
    if isinstance(s, PrintsStmt):
      if s.prints.reversible:
        raise SmvUnsupported("reversible read/write")
      return loc  # printing does not touch the store
    if isinstance(s, AssignStmt):
      return self._assign(s, env, loc)
    if isinstance(s, SwapStmt):
      left = self._lval_name(s.left, env)
      right = self._lval_name(s.right, env)
      out = self._loc()
      self._emit(loc, "TRUE", ((left, right), (right, left)), out)
      return out
    if isinstance(s, AssertStmt):
      cond, ok = self._cond(s.expr, env)
      out = self._loc()
      self._emit(loc, self._conj([ok, cond]), (), out)
      self._err(loc, f"!({self._conj([ok, cond])})")
      return out
    if isinstance(s, IfStmt):
      return self._if(s, env, loc, depth)
    if isinstance(s, FromStmt):
      return self._from(s, env, loc, depth)
    if isinstance(s, LocalStmt):
      return self._local(s, env, loc, depth)
    if isinstance(s, (CallStmt, UncallStmt)):
      return self._call(s, env, loc, depth, isinstance(s, UncallStmt))
    raise SmvUnsupported(f"statement outside the fragment: {type(s).__name__}")

  def _assign(self, s: AssignStmt, env: dict[str, str], loc: int) -> int:
    target = self._lval_name(s.lval, env)
    if self._occurs(target, s.expr, env):
      # `x += x` is not injective, and Janus rejects it *at run time* — after
      # inlining, `call bar(x, x); a += b` resolves to exactly this.  Reaching
      # the statement is the error, so it becomes an unconditional edge to ERR.
      out = self._loc()
      self._err(loc, "TRUE")
      return out
    obl: list[str] = []
    rhs = self._iexpr(s.expr, env, obl)
    if s.mod_op is ModOp.ADD_EQ:
      update = f"({target} + {rhs})"
    elif s.mod_op is ModOp.SUB_EQ:
      update = f"({target} - {rhs})"
    elif s.mod_op is ModOp.MUL_EQ:
      obl.append(f"({rhs}) != 0")  # x *= 0 is not injective
      update = f"({target} * {rhs})"
    elif s.mod_op is ModOp.DIV_EQ:
      obl.append(f"({rhs}) != 0")
      quotient, remainder = self._div_defines(target, rhs)
      obl.append(f"{remainder} = 0")  # `/=` must divide exactly
      update = quotient
    else:
      raise SmvUnsupported(f"assignment operator outside the fragment: {s.mod_op.value}")
    guard = self._conj(obl)
    out = self._loc()
    self._emit(loc, guard, ((target, update),), out)
    if guard != "TRUE":
      self._err(loc, f"!({guard})")
    return out

  def _if(self, s: IfStmt, env: dict[str, str], loc: int, depth: int) -> int:
    entry, entry_ok = self._cond(s.entry_cond, env)
    then_loc, else_loc, out = self._loc(), self._loc(), self._loc()
    self._emit(loc, self._conj([entry_ok, entry]), (), then_loc)
    self._emit(loc, self._conj([entry_ok, f"!({entry})"]), (), else_loc)
    if entry_ok != "TRUE":
      self._err(loc, f"!({entry_ok})")
    for branch, body, taken in ((then_loc, s.if_part, True), (else_loc, s.else_part, False)):
      end = self._stmts(body, env, branch, depth)
      exit_cond, exit_ok = self._cond(s.exit_cond, env)
      expected = exit_cond if taken else f"!({exit_cond})"
      self._emit(end, self._conj([exit_ok, expected]), (), out)
      self._err(end, f"!({self._conj([exit_ok, expected])})")
    return out

  def _from(self, s: FromStmt, env: dict[str, str], loc: int, depth: int) -> int:
    """`from e1 do S1 loop S2 until e2` = assert e1; S1; while !e2 { S2; assert !e1; S1 }."""
    entry, entry_ok = self._cond(s.entry_cond, env)
    top, out = self._loc(), self._loc()
    self._emit(loc, self._conj([entry_ok, entry]), (), top)
    self._err(loc, f"!({self._conj([entry_ok, entry])})")

    after_do = self._stmts(s.do_part, env, top, depth)
    exit_cond, exit_ok = self._cond(s.exit_cond, env)
    again = self._loc()
    self._emit(after_do, self._conj([exit_ok, exit_cond]), (), out)
    self._emit(after_do, self._conj([exit_ok, f"!({exit_cond})"]), (), again)
    if exit_ok != "TRUE":
      self._err(after_do, f"!({exit_ok})")

    after_loop = self._stmts(s.loop_part, env, again, depth)
    back, back_ok = self._cond(s.entry_cond, env)
    self._emit(after_loop, self._conj([back_ok, f"!({back})"]), (), top)
    self._err(after_loop, f"!({self._conj([back_ok, f'!({back})'])})")
    return out

  def _local(self, s: LocalStmt, env: dict[str, str], loc: int, depth: int) -> int:
    enter, leave = s.enter_decl, s.exit_decl
    for decl in (enter, leave):
      if decl.dimensions or decl.typ.kind != "int":
        raise SmvUnsupported("non-scalar local")
      if decl.decl_type is DeclType.CONSTANT:
        raise SmvUnsupported("constant local")
    if enter.ident.name != leave.ident.name:
      # Another run-time check: PyJanus raises when it reaches the `delocal`.
      out = self._loc()
      self._err(loc, "TRUE")
      return out
    obl: list[str] = []
    init = self._iexpr(enter.init_expr, env, obl) if enter.init_expr is not None else "0"
    name = self._declare(enter.ident.name, None)
    guard = self._conj(obl)
    body_loc = self._loc()
    self._emit(loc, guard, ((name, init),), body_loc)
    if guard != "TRUE":
      self._err(loc, f"!({guard})")

    inner = dict(env)
    inner[enter.ident.name] = name
    end = self._stmts(s.body, inner, body_loc, depth)

    obl2: list[str] = []
    final = self._iexpr(leave.init_expr, inner, obl2) if leave.init_expr is not None else "0"
    check = self._conj(obl2 + [f"{name} = {final}"])
    out = self._loc()
    self._emit(end, check, (), out)
    self._err(end, f"!({check})")
    return out

  def _call(self, s, env: dict[str, str], loc: int, depth: int, invert: bool) -> int:
    if s.external:
      raise SmvUnsupported("external call")
    proc = self.procs.get(s.ident.name)
    if proc is None:
      raise SmvUnsupported(f"undefined procedure: {s.ident.name}")
    if depth >= self.max_depth:
      self._bound(loc)
      return self._loc()  # unreachable continuation; keeps the caller's shape
    inner: dict[str, str] = {}
    for param, arg in zip(proc.params, s.args):
      if param.dimensions or param.typ.kind != "int":
        raise SmvUnsupported("non-scalar parameter")
      if not isinstance(arg, LvalExpr) or arg.lval.selectors:
        raise SmvUnsupported("argument is not a plain variable")
      resolved = self._lookup(arg.lval.ident.name, env)
      if resolved in inner.values():
        out = self._loc()  # two parameters bound to the same variable
        self._err(loc, "TRUE")
        return out
      inner[param.ident.name] = resolved
    body = invert_stmts(proc.body, False) if invert else proc.body
    return self._stmts(body, inner, loc, depth + 1)

  # -- driver ----------------------------------------------------------

  def run(self) -> str:
    main = self.program.main
    assert main is not None
    env: dict[str, str] = {}
    for decl in main.vdecls:
      if decl.dimensions or decl.typ.kind != "int":
        raise SmvUnsupported(f"non-scalar declaration: {decl.ident.name}")
      if decl.init_expr is not None:
        obl: list[str] = []
        init = self._iexpr(decl.init_expr, env, obl)
        if obl:
          raise SmvUnsupported("division in a declaration initializer")
      else:
        init = "0" if self.init_mode == "zero" else None
      env[decl.ident.name] = self._declare(decl.ident.name, init)
    entry = self._loc()
    final = self._stmts(main.stmts, env, entry, 0)
    return self._render(entry, final)

  def _render(self, entry: int, final: int) -> str:
    live = {t.src for t in self.trans}
    for loc in range(_FIRST_LOC, self._next_loc):
      if loc not in live:
        self._emit(loc, "TRUE", (), loc)  # halt: every location must be total
    if self.uses_err:
      self._emit(ERR_LOC, "TRUE", (), ERR_LOC)
    if self.uses_bound:
      self._emit(BOUND_LOC, "TRUE", (), BOUND_LOC)

    lines = ["MODULE main", "VAR", f"  pc : {ERR_LOC}..{self._next_loc - 1};"]
    for name in self.varnames:
      lines.append(f"  {name} : integer;")
    lines.append("")
    lines.append(f"-- pc = {ERR_LOC} : a Janus runtime assertion failed (ERR)")
    if self.uses_bound:
      lines.append(f"-- pc = {BOUND_LOC} : the inlining bound was hit (BOUND) —"
                   " a proof below is only valid up to that depth")
    lines.append(f"-- pc = {entry} : entry,  pc = {final} : normal termination")
    lines.append("")
    if self.defines:
      lines.append("DEFINE")
      for name, body in self.defines:
        lines.append(f"  {name} := {body};")
      lines.append("")
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
    lines.append(f"INVARSPEC pc != {ERR_LOC}")
    if self.uses_bound:
      lines.append(f"INVARSPEC pc != {BOUND_LOC}")
    return "\n".join(lines) + "\n"


def compile_to_smv(program: Program, *, init: str = "any", assume: str | None = None,
                   max_depth: int = 16) -> str:
  """Compile `program` to an nuXmv model asserting that no assertion can fail.

  `init` is `"any"` (variables unconstrained — proves totality on the whole
  domain) or `"zero"` (the store PyJanus actually starts from).  `assume` is an
  SMV boolean expression restricting the initial store, i.e. a precondition.
  `max_depth` bounds procedure inlining; if the bound is reachable the model
  says so through the `BOUND` location and the proof is only valid below it.
  """
  if init not in ("any", "zero"):
    raise ValueError(f"init must be 'any' or 'zero', not {init!r}")
  return _Compiler(program, init, assume, max_depth).run()
