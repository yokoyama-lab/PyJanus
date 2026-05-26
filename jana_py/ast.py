from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum


@dataclass(frozen=True)
class SourcePos:
  filename: str
  line: int
  column: int


class IntType(Enum):
  FRESH_VAR = "FreshVar"
  UNBOUND = "Unbound"
  I8 = "I8"
  I16 = "I16"
  I32 = "I32"
  I64 = "I64"
  U8 = "U8"
  U16 = "U16"
  U32 = "U32"
  U64 = "U64"
  INFER_INT = "InferInt"


class DeclType(Enum):
  VARIABLE = "Variable"
  ANCILLA = "Ancilla"
  CONSTANT = "Constant"


class ModOp(Enum):
  ADD_EQ = "+="
  SUB_EQ = "-="
  XOR_EQ = "^="
  MUL_EQ = "*="
  DIV_EQ = "/="


class UnaryOpKind(Enum):
  NOT = "!"
  BW_NEG = "~"


class BinOpKind(Enum):
  ADD = "+"
  SUB = "-"
  MUL = "*"
  DIV = "/"
  MOD = "%"
  EXP = "**"
  AND = "&"
  OR = "|"
  XOR = "^"
  SL = "<<"
  SR = ">>"
  LAND = "&&"
  LOR = "||"
  GT = ">"
  LT = "<"
  EQ = "=="
  NEQ = "!="
  GE = ">="
  LE = "<="


@dataclass(frozen=True)
class Type:
  kind: str
  pos: SourcePos
  int_type: IntType | None = None
  is_char: bool = False
  name: str | None = None


@dataclass(frozen=True)
class Ident:
  name: str
  pos: SourcePos


class LvalSelector:
  pass


@dataclass(frozen=True)
class LvalIndex(LvalSelector):
  expr: "Expr"


@dataclass(frozen=True)
class LvalField(LvalSelector):
  ident: Ident


@dataclass(frozen=True)
class Lval:
  ident: Ident
  selectors: list[LvalSelector] = field(default_factory=list)

  @property
  def indices(self) -> list["Expr"]:
    return [selector.expr for selector in self.selectors if isinstance(selector, LvalIndex)]

  @property
  def fields(self) -> list[Ident]:
    return [selector.ident for selector in self.selectors if isinstance(selector, LvalField)]


class Expr:
  pos: SourcePos


@dataclass(frozen=True)
class Number(Expr):
  value: int
  pos: SourcePos


@dataclass(frozen=True)
class Boolean(Expr):
  value: bool
  pos: SourcePos


@dataclass(frozen=True)
class LvalExpr(Expr):
  lval: Lval
  pos: SourcePos


@dataclass(frozen=True)
class UnaryExpr(Expr):
  op: UnaryOpKind
  expr: Expr
  pos: SourcePos


@dataclass(frozen=True)
class TypeCastExpr(Expr):
  typ: Type
  expr: Expr
  pos: SourcePos


@dataclass(frozen=True)
class BinExpr(Expr):
  op: BinOpKind
  left: Expr
  right: Expr
  pos: SourcePos


@dataclass(frozen=True)
class TernaryExpr(Expr):
  cond: Expr
  then_expr: Expr
  else_expr: Expr
  pos: SourcePos


@dataclass(frozen=True)
class EmptyExpr(Expr):
  ident: Ident
  pos: SourcePos


@dataclass(frozen=True)
class TopExpr(Expr):
  ident: Ident
  pos: SourcePos


@dataclass(frozen=True)
class SizeExpr(Expr):
  ident: Ident
  pos: SourcePos


@dataclass(frozen=True)
class NilExpr(Expr):
  pos: SourcePos


@dataclass(frozen=True)
class ArrayExpr(Expr):
  items: list[Expr]
  pos: SourcePos


@dataclass(frozen=True)
class StringLiteral(Expr):
  value: str
  pos: SourcePos


@dataclass(frozen=True)
class StructField:
  typ: Type
  ident: Ident
  pos: SourcePos
  dimensions: list["Expr | None"] = field(default_factory=list)


@dataclass(frozen=True)
class StructDef:
  ident: Ident
  fields: list[StructField]
  pos: SourcePos


@dataclass(frozen=True)
class Vdecl:
  decl_type: DeclType
  typ: Type
  ident: Ident
  dimensions: list[Expr | None]
  init_expr: Expr | None
  pos: SourcePos


@dataclass(frozen=True)
class LocalDecl:
  decl_type: DeclType
  typ: Type
  ident: Ident
  dimensions: list[Expr | None]
  init_expr: Expr | None
  pos: SourcePos


@dataclass(frozen=True)
class Prints:
  kind: str
  text: str | None = None
  args: list[Ident | Lval] = field(default_factory=list)


class Stmt:
  pos: SourcePos


@dataclass(frozen=True)
class AssignStmt(Stmt):
  mod_op: ModOp
  lval: Lval
  expr: Expr
  pos: SourcePos


@dataclass(frozen=True)
class IfStmt(Stmt):
  entry_cond: Expr
  if_part: list[Stmt]
  else_part: list[Stmt]
  exit_cond: Expr
  pos: SourcePos


@dataclass(frozen=True)
class FromStmt(Stmt):
  entry_cond: Expr
  do_part: list[Stmt]
  loop_part: list[Stmt]
  exit_cond: Expr
  pos: SourcePos


@dataclass(frozen=True)
class IterateStmt(Stmt):
  typ: Type
  ident: Ident
  start_expr: Expr
  step_expr: Expr
  end_expr: Expr
  body: list[Stmt]
  pos: SourcePos
  exclusive: bool = False  # True for C-style `for (i < end)`, False for `iterate i to end`


@dataclass(frozen=True)
class PushStmt(Stmt):
  expr: Expr
  ident: Ident
  pos: SourcePos


@dataclass(frozen=True)
class PopStmt(Stmt):
  expr: Expr
  ident: Ident
  pos: SourcePos


@dataclass(frozen=True)
class LocalStmt(Stmt):
  enter_decl: LocalDecl
  body: list[Stmt]
  exit_decl: LocalDecl
  pos: SourcePos


@dataclass(frozen=True)
class BareLocalStmt(Stmt):
  """Standalone local: allocates variable, body runs until block boundary.
  Used when delocal appears at a different nesting level (crossing pattern)."""
  decl: LocalDecl
  body: list[Stmt]
  pos: SourcePos


@dataclass(frozen=True)
class BareDelocalStmt(Stmt):
  """Standalone delocal: asserts value and deallocates variable.
  Pairs with a BareLocalStmt at a different nesting level."""
  decl: LocalDecl
  pos: SourcePos


@dataclass(frozen=True)
class CallStmt(Stmt):
  ident: Ident
  args: list[Expr]
  external: bool
  pos: SourcePos


@dataclass(frozen=True)
class UncallStmt(Stmt):
  ident: Ident
  args: list[Expr]
  external: bool
  pos: SourcePos


@dataclass(frozen=True)
class UserErrorStmt(Stmt):
  message: str
  pos: SourcePos


@dataclass(frozen=True)
class SwapStmt(Stmt):
  left: Lval
  right: Lval
  pos: SourcePos


@dataclass(frozen=True)
class PrintsStmt(Stmt):
  prints: Prints
  pos: SourcePos


@dataclass(frozen=True)
class SkipStmt(Stmt):
  pos: SourcePos


@dataclass(frozen=True)
class AssertStmt(Stmt):
  expr: Expr
  pos: SourcePos


@dataclass(frozen=True)
class SwitchCase:
  value: Expr
  body: list[Stmt]
  pos: SourcePos


@dataclass(frozen=True)
class SwitchStmt(Stmt):
  expr: Expr
  cases: list[SwitchCase]
  default_part: list[Stmt]
  exit_expr: Expr
  pos: SourcePos


@dataclass(frozen=True)
class AncillaBlockStmt(Stmt):
  decls: list[LocalDecl]
  body: list[Stmt]
  pos: SourcePos


@dataclass(frozen=True)
class ForeachStmt(Stmt):
  typ: Type
  ident: Ident
  array_expr: Expr
  body: list[Stmt]
  pos: SourcePos


@dataclass(frozen=True)
class ProcMain:
  vdecls: list[Vdecl]
  stmts: list[Stmt]
  pos: SourcePos


@dataclass(frozen=True)
class Proc:
  procname: Ident
  params: list[Vdecl]
  body: list[Stmt]


@dataclass(frozen=True)
class Program:
  main: ProcMain | None
  procs: list[Proc]
  struct_defs: list[StructDef] = field(default_factory=list)
