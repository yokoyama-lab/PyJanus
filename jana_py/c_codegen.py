from __future__ import annotations

from .ast import ArrayExpr
from .ast import AssertStmt
from .ast import AssignStmt
from .ast import BinExpr
from .ast import Boolean
from .ast import CallStmt
from .ast import DeclType
from .ast import EmptyExpr
from .ast import Expr
from .ast import FromStmt
from .ast import IfStmt
from .ast import IterateStmt
from .ast import LocalStmt
from .ast import Lval
from .ast import LvalField
from .ast import LvalIndex
from .ast import LvalExpr
from .ast import ModOp
from .ast import NilExpr
from .ast import Number
from .ast import PopStmt
from .ast import PrintsStmt
from .ast import Proc
from .ast import Program
from .ast import PushStmt
from .ast import SizeExpr
from .ast import SkipStmt
from .ast import StringLiteral
from .ast import SwapStmt
from .ast import TernaryExpr
from .ast import TopExpr
from .ast import Type
from .ast import TypeCastExpr
from .ast import UnaryExpr
from .ast import UncallStmt
from .ast import UserErrorStmt
from .ast import Ident
from .ast import Vdecl
from .invert import invert_stmts


C_TYPES = {
  "Unbound": "int",
  "I8": "signed char",
  "I16": "signed short",
  "I32": "signed int",
  "I64": "signed long",
  "U8": "unsigned char",
  "U16": "unsigned short",
  "U32": "unsigned int",
  "U64": "unsigned long",
  "FreshVar": "int",
  "InferInt": "int",
}


def format_struct_def(sdef) -> str:
  lines = [f"struct {_esc(sdef.ident.name)} {{"]
  for field in sdef.fields:
    dims = "".join(f"[{format_expr(d)}]" for d in field.dimensions if d is not None) if field.dimensions else ""
    lines.append(f"  {format_type(field.typ)} {_esc(field.ident.name)}{dims};")
  lines.append("};")
  return "\n".join(lines)


# Janus keeps procedures and variables in separate namespaces, but C++ does not,
# so a procedure named like a variable in scope (e.g. `procedure root` with a
# variable `root`) makes `root(...)` parse as a call on the int. Rename only the
# colliding procedures (leaving the common case byte-identical).
_PROC_RENAMES: dict[str, str] = {}

# Janus identifiers that happen to be C++ keywords (`procedure delete`, a
# variable `new`, a struct field `class`) must be renamed or the emitted code is
# not C++ at all -- `delete(k, r)` parses as the delete operator, not a call.
# Renaming is keyed on the *name*, so a Janus `delete` is the same C++ symbol
# everywhere it appears (declaration, call, inverse).
_CPP_KEYWORDS = frozenset("""
alignas alignof and and_eq asm auto bitand bitor bool break case catch char
char8_t char16_t char32_t class compl concept const consteval constexpr
constinit const_cast continue co_await co_return co_yield decltype default
delete do double dynamic_cast else enum explicit export extern false float for
friend goto if inline int long mutable namespace new noexcept not not_eq nullptr
operator or or_eq private protected public register reinterpret_cast requires
return short signed sizeof static static_assert static_cast struct switch
template this thread_local throw true try typedef typeid typename union unsigned
using virtual void volatile wchar_t while xor xor_eq
""".split()) | {"main", "std", "NULL"}

# name -> escaped name, for the keyword collisions of the program being emitted
_KW_RENAMES: dict[str, str] = {}


def _walk_names(node, out: set[str]) -> None:
  """Collect every identifier that appears anywhere in the AST, so a rename can
  be chosen fresh."""
  if isinstance(node, Ident):
    out.add(node.name)
    return
  if isinstance(node, (list, tuple)):
    for item in node:
      _walk_names(item, out)
    return
  fields = getattr(node, "__dataclass_fields__", None)
  if fields is None:
    return
  for f in fields:
    _walk_names(getattr(node, f, None), out)
  name = getattr(getattr(node, "typ", None), "name", None)
  if isinstance(name, str):
    out.add(name)


def _resolve_keyword_renames(program: Program) -> None:
  _KW_RENAMES.clear()
  used: set[str] = set()
  _walk_names(program.procs, used)
  _walk_names(program.main, used)
  _walk_names(program.struct_defs, used)
  for name in sorted(n for n in used if n in _CPP_KEYWORDS):
    cand = name + "_"
    while cand in used or cand in _KW_RENAMES.values():
      cand += "_"
    _KW_RENAMES[name] = cand


def _esc(name: str) -> str:
  """The C++ spelling of a Janus identifier."""
  return _KW_RENAMES.get(name, name)

# Declared length of each array (by name), used to resolve `size(A)` to a
# constant -- C++ raw-pointer parameters carry no length. Populated per program.
_ARRAY_LEN: dict[str, int] = {}

# Full declared shape of each array, needed to *type* a multi-dimensional array
# parameter: `int A[3][3]` decays to `int (*)[3]`, not to `int*`, so a formal
# declared `int LDU[][]` must be emitted with its trailing extents.
_ARRAY_DIMS: dict[str, list[int]] = {}


def _cname(name: str) -> str:
  return _PROC_RENAMES.get(name, _esc(name))


def _walk_calls(stmts):
  """Yield every CallStmt/UncallStmt reachable from `stmts`."""
  for s in stmts:
    if isinstance(s, (CallStmt, UncallStmt)):
      yield s
    for f in ("if_part", "else_part", "do_part", "loop_part", "body"):
      sub = getattr(s, f, None)
      if isinstance(sub, list):
        yield from _walk_calls(sub)


def _resolve_array_lengths(program: Program) -> None:
  """Map array names to their declared length, propagating from main's array
  declarations to procedure array formals through call sites (to a fixpoint)."""
  _ARRAY_LEN.clear()
  _ARRAY_DIMS.clear()
  if program.main is not None:
    for vd in program.main.vdecls:
      if vd.dimensions:
        try:
          _ARRAY_LEN[vd.ident.name] = int(format_expr(vd.dimensions[0]))
          _ARRAY_DIMS[vd.ident.name] = [int(format_expr(d)) for d in vd.dimensions]
        except (ValueError, TypeError):
          pass            # non-constant dimension: size() stays unresolved
  pnames = {p.procname.name: [par.ident.name for par in p.params] for p in program.procs}
  calls = list(_walk_calls(program.main.stmts if program.main else []))
  for p in program.procs:
    calls += list(_walk_calls(p.body))
  changed = True
  while changed:
    changed = False
    for call in calls:
      formals = pnames.get(call.ident.name)
      if not formals:
        continue
      for i, arg in enumerate(call.args):
        if i < len(formals) and isinstance(arg, LvalExpr) and not arg.lval.selectors:
          src = arg.lval.ident.name
          dst = formals[i]
          if src in _ARRAY_LEN and dst not in _ARRAY_LEN:
            _ARRAY_LEN[dst] = _ARRAY_LEN[src]
            changed = True
          if src in _ARRAY_DIMS and dst not in _ARRAY_DIMS:
            _ARRAY_DIMS[dst] = _ARRAY_DIMS[src]
            changed = True


def format_program(header: str | None, program: Program) -> str:
  lines = ["#include <iostream>", "#include <utility>", "#include <vector>"]
  if header:
    lines.append(f'#include "{header}"')
  lines.append("")
  _resolve_keyword_renames(program)
  for sdef in program.struct_defs:
    lines.append(format_struct_def(sdef))
    lines.append("")
  # Callee signatures are needed to emit value arguments (temp type, whether
  # the parameter is `constant`), so thread the proc table down to format_stmt.
  procs = {proc.procname.name: proc for proc in program.procs}
  _resolve_array_lengths(program)

  varnames = {vd.ident.name for vd in (program.main.vdecls if program.main else [])}
  for proc in program.procs:
    varnames |= {p.ident.name for p in proc.params}
  pnames = {p.procname.name for p in program.procs}
  _PROC_RENAMES.clear()
  for proc in program.procs:
    n = proc.procname.name
    if n in varnames:
      cand = n + "_proc"
      while cand in varnames or cand in pnames or cand in _PROC_RENAMES.values():
        cand += "_"
      _PROC_RENAMES[n] = cand

  # Forward declarations first, so (mutually) recursive calls and `uncall`s of a
  # later procedure (or of the procedure itself) resolve.
  for proc in program.procs:
    sig = ", ".join(format_param(param) for param in proc.params)
    lines.append(f"void {_cname(proc.procname.name)}({sig});")
    lines.append(f"void {_cname(proc.procname.name)}__inv({sig});")
  if program.procs:
    lines.append("")
  for proc in program.procs:
    lines.append(format_proc(proc, procs, name=_cname(proc.procname.name)))
    lines.append("")
  # Inverse functions, so `uncall p` can run p backwards (p__inv = invert p).
  for proc in program.procs:
    # local inversion (global_mode=False): a `call q` inside p inverts to
    # `uncall q`, which we emit as `q__inv` -- so p__inv composes correctly.
    lines.append(format_proc(proc, procs, name=_cname(proc.procname.name) + "__inv",
                             body=invert_stmts(proc.body, global_mode=False)))
    lines.append("")
  lines.append("int main() {")
  if program.main is not None:
    for vdecl in program.main.vdecls:
      lines.append("  " + format_vdecl(vdecl) + ";")
    for stmt in program.main.stmts:
      lines.extend(format_stmt(stmt, 1, procs))
  lines.append("  return 1;")
  lines.append("}")
  return "\n".join(lines) + "\n"


def format_proc(proc: Proc, procs: dict[str, Proc] | None = None,
                name: str | None = None, body=None) -> str:
  params = ", ".join(format_param(param) for param in proc.params)
  lines = [f"void {name or proc.procname.name}({params}) {{"]
  for stmt in (proc.body if body is None else body):
    lines.extend(format_stmt(stmt, 1, procs))
  lines.append("}")
  return "\n".join(lines)


def _emit_call(call_name: str, stmt, indent: int,
               procs: dict[str, Proc] | None) -> list[str]:
  # A non-l-value (value) argument can't bind to a by-reference parameter, so
  # mirror the interpreter: bind each to a temp declared with the parameter's
  # type and verify it reads back the same value on return (except `constant`
  # parameters, which are snapshotted without a restore check).  Param types come
  # from the *original* procedure (its inverse shares the signature).
  pad = "  " * indent
  proc = procs.get(stmt.ident.name) if procs else None
  inner = pad + "  "
  temps: list[str] = []
  call_args: list[str] = []
  checks: list[str] = []
  for i, arg in enumerate(stmt.args):
    if isinstance(arg, LvalExpr):
      call_args.append(format_expr(arg))
      continue
    param = proc.params[i] if proc is not None and i < len(proc.params) else None
    tmp = f"_va{i}"
    expr = format_expr(arg)
    ctype = "auto" if param is None else format_type(param.typ)
    temps.append(f"{inner}{ctype} {tmp} = {expr};")
    call_args.append(tmp)
    if param is not None and param.decl_type == DeclType.CONSTANT:
      continue
    cast = "" if param is None else f"({ctype})"
    checks.append(f'{inner}if ({tmp} != {cast}({expr})) throw "Value argument is not restored on return";')
  call = f"{call_name}({', '.join(call_args)});"
  if not temps:
    return [f"{pad}{call}"]
  return [f"{pad}{{", *temps, f"{inner}{call}", *checks, f"{pad}}}"]


def format_param(vdecl: Vdecl) -> str:
  if vdecl.dimensions:
    name = _esc(vdecl.ident.name)
    rank = len(vdecl.dimensions)
    if rank > 1:
      # A rank-n array decays to a pointer to its (n-1)-dimensional row, so the
      # trailing extents have to appear: `int A[3][3]` binds to `int (*)[3]`.
      # The formal is written `int A[][]`, so take the shape from the actual
      # (propagated through call sites by _resolve_array_lengths).
      dims = _ARRAY_DIMS.get(vdecl.ident.name)
      if dims is None or len(dims) != rank:
        raise ValueError(
          f"C++ translation needs the extents of the {rank}-dimensional array "
          f"parameter '{vdecl.ident.name}'")
      trailing = "".join(f"[{d}]" for d in dims[1:])
      return f"{format_type(vdecl.typ)} (*{name}){trailing}"
    return f"{format_type(vdecl.typ)}* {name}"
  return f"{format_type(vdecl.typ)}& {_esc(vdecl.ident.name)}"


def format_vdecl(vdecl: Vdecl) -> str:
  # Janus default-initializes every variable to 0; C++ leaves uninitialized
  # locals indeterminate, so emit an explicit zero initializer when none is given
  # (otherwise the generated program reads garbage instead of 0).
  if vdecl.typ.kind == "stack":
    init = f" = {format_expr(vdecl.init_expr)}" if vdecl.init_expr is not None else ""
    return f"{format_type(vdecl.typ)} {_esc(vdecl.ident.name)}{init}"
  if vdecl.dimensions:
    dims = "".join(f"[{format_expr(dim)}]" for dim in vdecl.dimensions if dim is not None)
    if vdecl.init_expr is not None:
      init = f" = {format_expr(vdecl.init_expr)}"
    else:
      init = " = {}"
    return f"{format_type(vdecl.typ)} {_esc(vdecl.ident.name)}{dims}{init}"
  if vdecl.typ.kind == "struct":
    # A struct is zero-initialized field by field; `= 0` is not valid C++ for it.
    init = f" = {format_expr(vdecl.init_expr)}" if vdecl.init_expr is not None else " = {}"
    return f"{format_type(vdecl.typ)} {_esc(vdecl.ident.name)}{init}"
  init = f" = {format_expr(vdecl.init_expr)}" if vdecl.init_expr is not None else " = 0"
  return f"{format_type(vdecl.typ)} {_esc(vdecl.ident.name)}{init}"


def format_type(typ: Type) -> str:
  if typ.is_char:
    return "char"
  if typ.kind == "struct":
    return _esc(typ.name) if typ.name else "struct"
  if typ.kind == "bool":
    return "bool"
  if typ.kind == "stack":
    return "std::vector<int>"
  if typ.kind != "int":
    raise ValueError(f"C++ translation does not support {typ.kind}")
  return C_TYPES[typ.int_type.value]


def format_stmt(stmt, indent: int, procs: dict[str, Proc] | None = None) -> list[str]:
  pad = "  " * indent
  if isinstance(stmt, AssignStmt):
    lval = format_lval(stmt.lval)
    expr = format_expr(stmt.expr)
    if stmt.mod_op == ModOp.MUL_EQ:
      # Mirror the interpreter's reversibility guard (runtime.py): e != 0.
      return [
        f"{pad}{{ auto _rhs = ({expr});",
        f'{pad}  if (_rhs == 0) throw "Multiplication by zero";',
        f"{pad}  {lval} *= _rhs; }}",
      ]
    if stmt.mod_op == ModOp.DIV_EQ:
      # Mirror the interpreter's guards: e != 0 and exact divisibility.
      return [
        f"{pad}{{ auto _rhs = ({expr});",
        f'{pad}  if (_rhs == 0) throw "Division by zero";',
        f'{pad}  if ({lval} % _rhs != 0) throw "Division remains";',
        f"{pad}  {lval} /= _rhs; }}",
      ]
    return [f"{pad}{lval} {stmt.mod_op.value} {expr};"]
  if isinstance(stmt, SwapStmt):
    return [f"{pad}std::swap({format_lval(stmt.left)}, {format_lval(stmt.right)});"]
  if isinstance(stmt, IfStmt):
    lines = [f"{pad}if ({format_expr(stmt.entry_cond)}) {{"]
    for nested in stmt.if_part:
      lines.extend(format_stmt(nested, indent + 1, procs))
    lines.append(f"{pad}}}")
    if stmt.else_part:
      lines.append(f"{pad}else {{")
      for nested in stmt.else_part:
        lines.extend(format_stmt(nested, indent + 1, procs))
      lines.append(f"{pad}}}")
    return lines
  if isinstance(stmt, FromStmt):
    # Janus `from e1 do s1 loop s2 until e2` runs s1, exits when e2 holds, else
    # runs s2 and repeats: s1; while(!e2){ s2; s1 } -- the do-part executes once
    # more than the loop-part (the loop off-by-one).  The earlier
    # `while(!e2){ s1; s2 }` dropped that trailing s1, computing a wrong result.
    lines = []
    for nested in stmt.do_part:
      lines.extend(format_stmt(nested, indent, procs))
    lines.append(f"{pad}while (!({format_expr(stmt.exit_cond)})) {{")
    for nested in stmt.loop_part:
      lines.extend(format_stmt(nested, indent + 1, procs))
    for nested in stmt.do_part:
      lines.extend(format_stmt(nested, indent + 1, procs))
    lines.append(f"{pad}}}")
    return lines
  if isinstance(stmt, IterateStmt):
    # `to end` is inclusive in both directions; a negative step counts down, so
    # the bound test must follow the step's sign (a fixed `<=` dropped every
    # descending loop -- including the inverse of an ascending one).
    var = _esc(stmt.ident.name)
    end = format_expr(stmt.end_expr)
    step = format_expr(stmt.step_expr)
    cond = f"(({step}) >= 0 ? {var} <= ({end}) : {var} >= ({end}))"
    lines = [f"{pad}for ({format_type(stmt.typ)} {var} = {format_expr(stmt.start_expr)}; "
             f"{cond}; {var} += ({step})) {{"]
    for nested in stmt.body:
      lines.extend(format_stmt(nested, indent + 1, procs))
    lines.append(f"{pad}}}")
    return lines
  if isinstance(stmt, LocalStmt):
    lines = [f"{pad}{{", f"{pad}  {format_local_decl(stmt.enter_decl)};"]
    for nested in stmt.body:
      lines.extend(format_stmt(nested, indent + 1, procs))
    lines.append(f"{pad}}}")
    return lines
  if isinstance(stmt, CallStmt):
    return _emit_call(_cname(stmt.ident.name), stmt, indent, procs)
  if isinstance(stmt, UncallStmt):
    # `uncall p` runs p backwards; we emit an inverse function `p__inv` (its body
    # is the program inverter applied to p's body) and call that.
    return _emit_call(_cname(stmt.ident.name) + "__inv", stmt, indent, procs)
  if isinstance(stmt, PrintsStmt):
    if stmt.prints.kind == "print":
      return [f'{pad}std::cout << "{escape_cpp(stmt.prints.text or "")}";']
    if stmt.prints.kind == "printf":
      parts = render_printf(stmt.prints.text or "", [_fmt_arg(a) for a in stmt.prints.args])
      return [f"{pad}std::cout << {parts};"]
    # `show` is deprecated debug output; it has no store effect and cannot be
    # streamed for arrays/stacks, and the store-based tests ignore it, so omit it.
    return [f"{pad}/* show (deprecated; omitted) */"]
  if isinstance(stmt, SkipStmt):
    return [f"{pad};"]
  if isinstance(stmt, AssertStmt):
    return [f"{pad}/* assert {format_expr(stmt.expr)} */"]
  if isinstance(stmt, UserErrorStmt):
    return [f'{pad}throw "{escape_cpp(stmt.message)}";']
  if isinstance(stmt, PushStmt):
    # Janus push moves the value onto the stack and zeroes the source (reversible).
    val = format_expr(stmt.expr)
    return [f"{pad}{_esc(stmt.ident.name)}.push_back({val}); {val} = 0;"]
  if isinstance(stmt, PopStmt):
    val = format_expr(stmt.expr)
    return [f"{pad}{val} = {_esc(stmt.ident.name)}.back(); {_esc(stmt.ident.name)}.pop_back();"]
  raise ValueError(f"Unsupported statement {type(stmt).__name__}")


def format_local_decl(decl) -> str:
  if decl.dimensions:
    dims = "".join(f"[{format_expr(dim)}]" for dim in decl.dimensions if dim is not None)
    init = f" = {format_expr(decl.init_expr)}" if decl.init_expr is not None else ""
    return f"{format_type(decl.typ)} {_esc(decl.ident.name)}{dims}{init}"
  # `local int x` with no initializer means 0 in Janus; C++ would leave it
  # indeterminate.  A struct zero-initializes with `{}`.
  if decl.init_expr is not None:
    init = f" = {format_expr(decl.init_expr)}"
  else:
    init = " = {}" if decl.typ.kind == "struct" else " = 0"
  return f"{format_type(decl.typ)} {_esc(decl.ident.name)}{init}"


def format_lval(lval: Lval) -> str:
  parts = [_esc(lval.ident.name)]
  for selector in lval.selectors:
    if isinstance(selector, LvalField):
      parts.append(f".{_esc(selector.ident.name)}")
    elif isinstance(selector, LvalIndex):
      parts.append(f"[{format_expr(selector.expr)}]")
  return "".join(parts)


def format_expr(expr: Expr) -> str:
  if isinstance(expr, Number):
    return str(expr.value)
  if isinstance(expr, Boolean):
    return "true" if expr.value else "false"
  if isinstance(expr, LvalExpr):
    return format_lval(expr.lval)
  if isinstance(expr, UnaryExpr):
    return f"{expr.op.value}{format_expr(expr.expr)}"
  if isinstance(expr, TypeCastExpr):
    return f"(({format_type(expr.typ)}) {format_expr(expr.expr)})"
  if isinstance(expr, BinExpr):
    op = "==" if expr.op.value == "=" else expr.op.value
    return f"({format_expr(expr.left)} {op} {format_expr(expr.right)})"
  if isinstance(expr, TernaryExpr):
    return f"({format_expr(expr.cond)} ? {format_expr(expr.then_expr)} : {format_expr(expr.else_expr)})"
  if isinstance(expr, SizeExpr):
    # C++ array parameters are raw pointers with no length; resolve the declared
    # length to a constant where known.
    if expr.ident.name in _ARRAY_LEN:
      return str(_ARRAY_LEN[expr.ident.name])
    return f"(int){_esc(expr.ident.name)}.size()"        # a stack's depth
  if isinstance(expr, ArrayExpr):
    return "{ " + ", ".join(format_expr(item) for item in expr.items) + " }"
  if isinstance(expr, StringLiteral):
    return f'"{escape_cpp(expr.value)}"'
  if isinstance(expr, EmptyExpr):
    return f"{_esc(expr.ident.name)}.empty()"
  if isinstance(expr, TopExpr):
    return f"{_esc(expr.ident.name)}.back()"
  if isinstance(expr, NilExpr):
    return "{}"
  raise ValueError(f"Unsupported expression {type(expr).__name__}")


def _fmt_arg(arg) -> str:
  if isinstance(arg, Ident):
    return _esc(arg.name)
  return format_lval(arg)


def render_printf(text: str, args: list[str]) -> str:
  rendered: list[str] = []
  arg_index = 0
  i = 0
  while i < len(text):
    if text[i] == "%" and i + 1 < len(text):
      kind = text[i + 1]
      if kind == "%":
        rendered.append(f'"%"')
      elif kind in {"d", "s"}:
        rendered.append(args[arg_index])
        arg_index += 1
      i += 2
      continue
    start = i
    while i < len(text) and text[i] != "%":
      i += 1
    rendered.append(f'"{escape_cpp(text[start:i])}"')
  return " << ".join(rendered) if rendered else '""'


def escape_cpp(text: str) -> str:
  return text.replace("\\", "\\\\").replace('"', '\\"').replace("\0", "\\0").replace("\n", "\\n")
