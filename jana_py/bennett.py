"""Bennett's automatic reversibilization (compute-copy-uncompute).

Given a sequence of (possibly irreversible) statements that compute
``f(inputs) -> outputs``, this module produces a reversible version using
Bennett's trick:

  1. **Forward** -- execute the original statements, using ancilla variables
     to store all intermediate values so the computation is recoverable.
  2. **Copy** -- XOR the desired output values onto fresh zero-initialised
     output variables (which makes them available outside the cleanup phase).
  3. **Uncompute** -- run the inverse of the forward statements to return
     all ancilla variables back to zero.

The result is a ``LocalStmt``-wrapped block:

    local <ancillas> = 0
        <forward_stmts>
        <copy: out ^= ancilla_out>
        <inverted forward_stmts>
    delocal <ancillas> = 0

Usage::

    from jana_py.bennett import bennett_embed

    stmts = [...]           # original computation
    output_map = {"y": "result"}  # ancilla name -> output variable name
    embedded = bennett_embed(stmts, output_map)
"""
from __future__ import annotations

from dataclasses import replace

from .ast import (
    AssignStmt,
    BinExpr,
    BinOpKind,
    DeclType,
    Expr,
    FromStmt,
    Ident,
    IfStmt,
    IntType,
    IterateStmt,
    LocalDecl,
    LocalStmt,
    Lval,
    LvalExpr,
    ModOp,
    Number,
    SourcePos,
    Stmt,
    SwapStmt,
    Type,
)
from .invert import invert_stmts


# Sentinel position used for synthesised AST nodes.
_POS = SourcePos("<bennett>", 0, 0)


def _int_type() -> Type:
    """Return the default ``int`` type for ancilla declarations."""
    return Type(kind="int", pos=_POS, int_type=IntType.I32)


def _ident(name: str) -> Ident:
    return Ident(name=name, pos=_POS)


def _lval(name: str) -> Lval:
    return Lval(ident=_ident(name))


def _lval_expr(name: str) -> LvalExpr:
    return LvalExpr(lval=_lval(name), pos=_POS)


def _zero() -> Number:
    return Number(value=0, pos=_POS)


# ---------------------------------------------------------------------------
# Variable collection
# ---------------------------------------------------------------------------

def _collect_modified_vars(stmts: list[Stmt]) -> set[str]:
    """Return the set of variable names modified (assigned/swapped) by *stmts*.

    This is a conservative over-approximation used to decide which variables
    need ancilla copies.
    """
    modified: set[str] = set()
    for stmt in stmts:
        if isinstance(stmt, AssignStmt):
            modified.add(stmt.lval.ident.name)
        elif isinstance(stmt, SwapStmt):
            modified.add(stmt.left.ident.name)
            modified.add(stmt.right.ident.name)
        elif isinstance(stmt, IfStmt):
            modified |= _collect_modified_vars(stmt.if_part)
            modified |= _collect_modified_vars(stmt.else_part)
        elif isinstance(stmt, FromStmt):
            modified |= _collect_modified_vars(stmt.do_part)
            modified |= _collect_modified_vars(stmt.loop_part)
        elif isinstance(stmt, IterateStmt):
            modified |= _collect_modified_vars(stmt.body)
        elif isinstance(stmt, LocalStmt):
            modified |= _collect_modified_vars(stmt.body)
    return modified


def _collect_read_vars_expr(expr: Expr) -> set[str]:
    """Return variable names read in *expr*."""
    if isinstance(expr, LvalExpr):
        return {expr.lval.ident.name}
    if isinstance(expr, BinExpr):
        return _collect_read_vars_expr(expr.left) | _collect_read_vars_expr(expr.right)
    return set()


# ---------------------------------------------------------------------------
# Variable renaming
# ---------------------------------------------------------------------------

def _rename_ident(ident: Ident, mapping: dict[str, str]) -> Ident:
    new_name = mapping.get(ident.name, ident.name)
    if new_name == ident.name:
        return ident
    return replace(ident, name=new_name)


def _rename_lval(lval: Lval, mapping: dict[str, str]) -> Lval:
    new_ident = _rename_ident(lval.ident, mapping)
    if new_ident is lval.ident:
        return lval
    return replace(lval, ident=new_ident)


def _rename_expr(expr: Expr, mapping: dict[str, str]) -> Expr:
    if isinstance(expr, LvalExpr):
        new_lval = _rename_lval(expr.lval, mapping)
        return replace(expr, lval=new_lval) if new_lval is not expr.lval else expr
    if isinstance(expr, BinExpr):
        new_left = _rename_expr(expr.left, mapping)
        new_right = _rename_expr(expr.right, mapping)
        if new_left is expr.left and new_right is expr.right:
            return expr
        return replace(expr, left=new_left, right=new_right)
    # Number, Boolean, etc. -- no variables to rename.
    return expr


def _rename_stmt(stmt: Stmt, mapping: dict[str, str]) -> Stmt:
    """Return *stmt* with all variable references renamed according to *mapping*."""
    if isinstance(stmt, AssignStmt):
        new_lval = _rename_lval(stmt.lval, mapping)
        new_expr = _rename_expr(stmt.expr, mapping)
        return replace(stmt, lval=new_lval, expr=new_expr)
    if isinstance(stmt, SwapStmt):
        new_left = _rename_lval(stmt.left, mapping)
        new_right = _rename_lval(stmt.right, mapping)
        return replace(stmt, left=new_left, right=new_right)
    if isinstance(stmt, IfStmt):
        return replace(
            stmt,
            entry_cond=_rename_expr(stmt.entry_cond, mapping),
            if_part=_rename_stmts(stmt.if_part, mapping),
            else_part=_rename_stmts(stmt.else_part, mapping),
            exit_cond=_rename_expr(stmt.exit_cond, mapping),
        )
    if isinstance(stmt, FromStmt):
        return replace(
            stmt,
            entry_cond=_rename_expr(stmt.entry_cond, mapping),
            do_part=_rename_stmts(stmt.do_part, mapping),
            loop_part=_rename_stmts(stmt.loop_part, mapping),
            exit_cond=_rename_expr(stmt.exit_cond, mapping),
        )
    if isinstance(stmt, IterateStmt):
        return replace(
            stmt,
            body=_rename_stmts(stmt.body, mapping),
        )
    if isinstance(stmt, LocalStmt):
        return replace(
            stmt,
            body=_rename_stmts(stmt.body, mapping),
        )
    return stmt


def _rename_stmts(stmts: list[Stmt], mapping: dict[str, str]) -> list[Stmt]:
    return [_rename_stmt(s, mapping) for s in stmts]


# ---------------------------------------------------------------------------
# Core: Bennett embedding
# ---------------------------------------------------------------------------

def bennett_embed(
    stmts: list[Stmt],
    output_map: dict[str, str],
    *,
    ancilla_prefix: str = "anc__",
    input_vars: list[str] | None = None,
) -> list[Stmt]:
    """Apply Bennett's compute-copy-uncompute trick.

    Parameters
    ----------
    stmts:
        The forward computation (may be irreversible).
    output_map:
        Mapping from variable names that hold computed results at the end of
        *stmts* to external output variable names that should receive copies.
        E.g. ``{"y": "result"}`` means "after forward execution the value in
        ``y`` should be XOR-copied to the variable ``result``".
    ancilla_prefix:
        Prefix for generated ancilla variable names.
    input_vars:
        If given, only these variables are treated as external inputs (and
        therefore renamed into ancilla copies for the forward phase).  If
        ``None``, the set is inferred from read-but-not-modified variables.

    Returns
    -------
    A list containing ``LocalStmt`` nodes that wrap the full
    compute-copy-uncompute sequence.  The caller is responsible for
    declaring the output variables (those in ``output_map.values()``)
    **outside** the returned block.
    """
    # 1. Determine which variables the computation modifies.
    modified = _collect_modified_vars(stmts)

    # 2. Build ancilla rename mapping: every variable modified by the
    #    computation gets an ancilla shadow.
    ancilla_names: dict[str, str] = {}  # original name -> ancilla name
    for var in sorted(modified):
        ancilla_names[var] = f"{ancilla_prefix}{var}"

    # 3. Rename statements so they operate on ancilla variables.
    forward_stmts = _rename_stmts(stmts, ancilla_names)

    # 4. Generate copy statements: out ^= ancilla_out
    copy_stmts: list[Stmt] = []
    for src_var, dst_var in sorted(output_map.items()):
        anc_name = ancilla_names.get(src_var, src_var)
        copy_stmts.append(
            AssignStmt(
                mod_op=ModOp.XOR_EQ,
                lval=_lval(dst_var),
                expr=_lval_expr(anc_name),
                pos=_POS,
            )
        )

    # 5. Generate uncompute: inverse of the forward computation.
    uncompute_stmts = invert_stmts(forward_stmts, global_mode=True)

    # 6. Build the body: forward + copy + uncompute
    body = forward_stmts + copy_stmts + uncompute_stmts

    # 7. Wrap in local/delocal for each ancilla variable.
    #    We nest them inside-out: the first ancilla declared is the outermost
    #    LocalStmt, so delocals come in reverse order (as required by Jana).
    result_body = body
    for _orig, anc in sorted(ancilla_names.items()):
        enter_decl = LocalDecl(
            decl_type=DeclType.VARIABLE,
            typ=_int_type(),
            ident=_ident(anc),
            dimensions=[],
            init_expr=_zero(),
            pos=_POS,
        )
        exit_decl = LocalDecl(
            decl_type=DeclType.VARIABLE,
            typ=_int_type(),
            ident=_ident(anc),
            dimensions=[],
            init_expr=_zero(),
            pos=_POS,
        )
        result_body = [LocalStmt(enter_decl=enter_decl, body=result_body, exit_decl=exit_decl, pos=_POS)]

    return result_body


def bennett_embed_procedure(
    stmts: list[Stmt],
    output_names: list[str],
    *,
    ancilla_prefix: str = "anc__",
) -> list[Stmt]:
    """Convenience wrapper: treat *output_names* as variables whose final
    values should be preserved (identity mapping).

    The output variables will receive copies via XOR, so they must be
    zero-initialised by the caller before entering the embedded block.
    """
    output_map = {name: name for name in output_names}
    return bennett_embed(stmts, output_map, ancilla_prefix=ancilla_prefix)
