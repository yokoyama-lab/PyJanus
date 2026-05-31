"""Encode a Janus-0 program into flat integer arrays for the self-interpreter.

Janus-0 subset: +=, -=, ^=, <=>, if/fi, from/until, call, uncall, skip,
local/delocal (variable only), and expressions (const, var, arr[idx], binop).

Encoding format for code[]:
  [TAG, TOTAL_LEN, ...payload..., TOTAL_LEN]
  TAG identifies the construct; TOTAL_LEN includes TAG and both LEN fields.

Usage:
  python3 -m jana_py.encode examples/fib.ja
"""

from __future__ import annotations

import sys
from dataclasses import dataclass, field

from .ast import (
    AssignStmt, BinExpr, BinOpKind, CallStmt, FromStmt, IfStmt,
    LvalExpr, Lval, LvalIndex, ModOp, Number, Proc, Program,
    SkipStmt, Stmt, SwapStmt, UncallStmt, LocalStmt, Expr,
)
from .parser_jana2014 import parse_program
from .preprocess import preprocess_text

# ── Tag constants (must match opcodes.ja) ─────────────────────────────
S_ADDEQ  = 1;  S_SUBEQ  = 2;  S_XOREQ  = 3;  S_SWAP   = 4
S_IF     = 5;  S_FROM   = 6;  S_CALL   = 7;  S_UNCALL = 8
S_SKIP   = 9;  S_BLOCK  = 10; S_SWITCH = 11

E_CONST  = 20; E_VAR    = 21; E_ARRIDX = 22; E_BINOP  = 23

L_VAR    = 30; L_ARRIDX = 31

# Binary operator codes
BINOP_MAP: dict[BinOpKind, int] = {
    BinOpKind.ADD: 1,  BinOpKind.SUB: 2,  BinOpKind.MUL: 3,
    BinOpKind.DIV: 4,  BinOpKind.MOD: 5,  BinOpKind.AND: 6,
    BinOpKind.OR:  7,  BinOpKind.XOR: 8,  BinOpKind.LT:  9,
    BinOpKind.GT:  10, BinOpKind.EQ:  11, BinOpKind.NEQ: 12,
    BinOpKind.LE:  13, BinOpKind.GE:  14, BinOpKind.LAND:15,
    BinOpKind.LOR: 16,
}

MODOP_TAG = {ModOp.ADD_EQ: S_ADDEQ, ModOp.SUB_EQ: S_SUBEQ, ModOp.XOR_EQ: S_XOREQ}


@dataclass
class VarSlot:
    """Maps a variable name to its store[] slot range."""
    slot: int
    size: int  # 1 for scalar, >1 for array


@dataclass
class ProcEntry:
    """Procedure table entry."""
    name: str
    code_offset: int       # offset into code[]
    stmt_count: int        # number of top-level statements
    param_names: list[str] # parameter names (for argument binding)


@dataclass
class EncodeResult:
    """Result of encoding a program."""
    code: list[int]
    store_size: int
    var_map: dict[str, VarSlot]
    procs: list[ProcEntry]
    main_stmt_count: int
    main_code_offset: int


class Encoder:
    """Encodes a Janus-0 AST into flat integer arrays."""

    def __init__(self) -> None:
        self.code: list[int] = []
        self.var_map: dict[str, VarSlot] = {}
        self.next_slot: int = 0
        self.procs: list[ProcEntry] = []
        self._proc_map: dict[str, ProcEntry] = {}
        self._loop_scratch_slots: list[int] = []  # scratch slots for loop go-flags

    def alloc_var(self, name: str, size: int = 1) -> int:
        """Allocate store slot(s) for a variable."""
        if name in self.var_map:
            return self.var_map[name].slot
        slot = self.next_slot
        self.var_map[name] = VarSlot(slot, size)
        self.next_slot += size
        return slot

    def slot_of(self, name: str) -> int:
        return self.var_map[name].slot

    # ── Expression encoding ───────────────────────────────────────────

    def encode_expr(self, expr: Expr) -> list[int]:
        if isinstance(expr, Number):
            body = [E_CONST, 4, expr.value, 4]
            return body

        if isinstance(expr, LvalExpr):
            return self.encode_lval_expr(expr.lval)

        if isinstance(expr, BinExpr):
            left = self.encode_expr(expr.left)
            right = self.encode_expr(expr.right)
            op_code = BINOP_MAP[expr.op]
            # [E_BINOP, len, op_code, left..., right..., len]
            payload = [op_code] + left + right
            total_len = 2 + len(payload) + 1  # tag + len + payload + len
            return [E_BINOP, total_len] + payload + [total_len]

        raise ValueError(f"Unsupported expression type: {type(expr).__name__}")

    def encode_lval_expr(self, lval: Lval) -> list[int]:
        name = lval.ident.name
        slot = self.slot_of(name)
        if not lval.selectors:
            return [E_VAR, 4, slot, 4]
        # Array indexing: a[expr]
        idx_expr = lval.selectors[0]
        if isinstance(idx_expr, LvalIndex):
            idx_code = self.encode_expr(idx_expr.expr)
            # [E_ARRIDX, len, base_slot, idx_expr..., len]
            payload = [slot] + idx_code
            total_len = 2 + len(payload) + 1
            return [E_ARRIDX, total_len] + payload + [total_len]
        raise ValueError(f"Unsupported lval selector: {type(idx_expr).__name__}")

    # ── Lvalue encoding (for assignment targets) ──────────────────────

    def encode_lval(self, lval: Lval) -> list[int]:
        name = lval.ident.name
        slot = self.slot_of(name)
        if not lval.selectors:
            return [L_VAR, 4, slot, 4]
        idx_expr = lval.selectors[0]
        if isinstance(idx_expr, LvalIndex):
            idx_code = self.encode_expr(idx_expr.expr)
            payload = [slot] + idx_code
            total_len = 2 + len(payload) + 1
            return [L_ARRIDX, total_len] + payload + [total_len]
        raise ValueError(f"Unsupported lval selector for assignment")

    # ── Statement encoding ────────────────────────────────────────────

    def encode_stmt(self, stmt: Stmt) -> list[int]:
        if isinstance(stmt, AssignStmt):
            return self._encode_assign(stmt)
        if isinstance(stmt, SwapStmt):
            return self._encode_swap(stmt)
        if isinstance(stmt, SkipStmt):
            return [S_SKIP, 4, 0, 4]
        if isinstance(stmt, IfStmt):
            return self._encode_if(stmt)
        if isinstance(stmt, FromStmt):
            return self._encode_from(stmt)
        if isinstance(stmt, CallStmt):
            return self._encode_call(stmt)
        if isinstance(stmt, UncallStmt):
            return self._encode_uncall(stmt)
        if isinstance(stmt, LocalStmt):
            return self._encode_local(stmt)
        raise ValueError(f"Unsupported statement type: {type(stmt).__name__}")

    def _encode_assign(self, stmt: AssignStmt) -> list[int]:
        tag = MODOP_TAG[stmt.mod_op]
        lval_code = self.encode_lval(stmt.lval)
        expr_code = self.encode_expr(stmt.expr)
        payload = lval_code + expr_code
        total_len = 2 + len(payload) + 1
        return [tag, total_len] + payload + [total_len]

    def _encode_swap(self, stmt: SwapStmt) -> list[int]:
        lval1 = self.encode_lval(stmt.left)
        lval2 = self.encode_lval(stmt.right)
        payload = lval1 + lval2
        total_len = 2 + len(payload) + 1
        return [S_SWAP, total_len] + payload + [total_len]

    def _encode_if(self, stmt: IfStmt) -> list[int]:
        cond_code = self.encode_expr(stmt.entry_cond)
        then_stmts = self.encode_block(stmt.if_part)
        else_stmts = self.encode_block(stmt.else_part)
        exit_code = self.encode_expr(stmt.exit_cond)
        # [S_IF, len, cond..., then_count, then_block_len, then...,
        #  else_count, else_block_len, else..., exit_cond..., len]
        payload = (
            cond_code
            + [len(stmt.if_part), len(then_stmts)] + then_stmts
            + [len(stmt.else_part), len(else_stmts)] + else_stmts
            + exit_code
        )
        total_len = 2 + len(payload) + 1
        return [S_IF, total_len] + payload + [total_len]

    def _encode_from(self, stmt: FromStmt) -> list[int]:
        entry_code = self.encode_expr(stmt.entry_cond)
        do_stmts = self.encode_block(stmt.do_part)
        loop_stmts = self.encode_block(stmt.loop_part)
        exit_code = self.encode_expr(stmt.exit_cond)
        # Allocate a scratch store slot for the loop go-flag
        gs = self.next_slot
        self.next_slot += 1
        self._loop_scratch_slots.append(gs)
        # [S_FROM, len, gs, entry..., do_count, do_block_len, do...,
        #  loop_count, loop_block_len, loop..., exit_cond..., len]
        payload = (
            [gs] + entry_code
            + [len(stmt.do_part), len(do_stmts)] + do_stmts
            + [len(stmt.loop_part), len(loop_stmts)] + loop_stmts
            + exit_code
        )
        total_len = 2 + len(payload) + 1
        return [S_FROM, total_len] + payload + [total_len]

    def _encode_call(self, stmt: CallStmt) -> list[int]:
        proc_name = stmt.ident.name
        # Encode argument slots
        arg_slots = [self._resolve_arg(a) for a in stmt.args]
        # [S_CALL, len, proc_index, #args, arg_slot..., len]
        payload = [self._proc_index(proc_name), len(arg_slots)] + arg_slots
        total_len = 2 + len(payload) + 1
        return [S_CALL, total_len] + payload + [total_len]

    def _encode_uncall(self, stmt: UncallStmt) -> list[int]:
        proc_name = stmt.ident.name
        arg_slots = [self._resolve_arg(a) for a in stmt.args]
        payload = [self._proc_index(proc_name), len(arg_slots)] + arg_slots
        total_len = 2 + len(payload) + 1
        return [S_UNCALL, total_len] + payload + [total_len]

    def _encode_local(self, stmt: LocalStmt) -> list[int]:
        # For local/delocal: allocate a fresh slot, encode body
        var_name = stmt.enter_decl.ident.name
        slot = self.alloc_var(var_name)
        init_code = self.encode_expr(stmt.enter_decl.init_expr)
        body_code = self.encode_block(stmt.body)
        exit_code = self.encode_expr(stmt.exit_decl.init_expr)
        # Re-encode as a special block that the interpreter handles
        # We expand local/delocal into: init store[slot], run body, check delocal
        # For simplicity, encode as a sequence:
        #   slot += init_expr; body; slot -= exit_expr  (if local is add-based)
        # But the proper approach: store init in slot, run body, assert slot = exit
        # We'll use a dedicated encoding later. For now, inline:
        #   S_ADDEQ slot init_expr | body_stmts | S_SUBEQ slot exit_expr
        # This works because local int x = E means x starts at E, and
        # delocal int x = E means x must equal E at exit (and is cleared).
        assign_in = [S_ADDEQ]
        lval_in = [L_VAR, 3, slot, 3]
        total_in = 2 + len(lval_in) + len(init_code) + 1
        assign_in = [S_ADDEQ, total_in] + lval_in + init_code + [total_in]

        assign_out = [S_SUBEQ]
        total_out = 2 + len(lval_in) + len(exit_code) + 1
        assign_out = [S_SUBEQ, total_out] + lval_in + exit_code + [total_out]

        return assign_in + body_code + assign_out

    def _resolve_arg(self, arg: Expr) -> int:
        """Resolve a call argument to a store slot."""
        if isinstance(arg, LvalExpr):
            return self.slot_of(arg.lval.ident.name)
        raise ValueError(f"Call arguments must be variables, got {type(arg).__name__}")

    def _proc_index(self, name: str) -> int:
        if name not in self._proc_map:
            raise ValueError(f"Unknown procedure: {name}")
        for i, p in enumerate(self.procs):
            if p.name == name:
                return i
        raise ValueError(f"Procedure not in list: {name}")

    # ── Block encoding ────────────────────────────────────────────────

    def encode_block(self, stmts: list[Stmt]) -> list[int]:
        result: list[int] = []
        for s in stmts:
            result.extend(self.encode_stmt(s))
        return result

    # ── Program encoding ──────────────────────────────────────────────

    def encode_program(self, program: Program) -> EncodeResult:
        # Phase 1: Allocate variable slots for main declarations
        if program.main:
            for vdecl in program.main.vdecls:
                name = vdecl.ident.name
                dims = vdecl.dimensions
                if dims:
                    # Array: extract size from first dimension
                    dim_expr = dims[0]
                    if isinstance(dim_expr, Number):
                        self.alloc_var(name, dim_expr.value)
                    else:
                        raise ValueError(f"Array size must be a constant for {name}")
                else:
                    self.alloc_var(name)

        # Phase 2: Register procedures (two-pass for forward references)
        for proc in program.procs:
            entry = ProcEntry(proc.procname.name, 0, len(proc.body),
                            [p.ident.name for p in proc.params])
            self.procs.append(entry)
            self._proc_map[proc.procname.name] = entry

        # Phase 2b: Allocate parameter slots for procedures
        for proc in program.procs:
            for param in proc.params:
                name = param.ident.name
                if name not in self.var_map:
                    dims = param.dimensions
                    if dims:
                        dim_expr = dims[0]
                        if isinstance(dim_expr, Number):
                            self.alloc_var(name, dim_expr.value)
                        else:
                            raise ValueError(f"Array param size must be constant: {name}")
                    else:
                        self.alloc_var(name)

        # Phase 3: Encode procedure bodies
        for i, proc in enumerate(program.procs):
            self.procs[i].code_offset = len(self.code)
            body_code = self.encode_block(proc.body)
            self.code.extend(body_code)

        # Phase 4: Encode main body
        main_offset = len(self.code)
        main_count = 0
        if program.main:
            main_code = self.encode_block(program.main.stmts)
            self.code.extend(main_code)
            main_count = len(program.main.stmts)

        return EncodeResult(
            code=self.code,
            store_size=self.next_slot,
            var_map=self.var_map,
            procs=self.procs,
            main_stmt_count=main_count,
            main_code_offset=main_offset,
        )


def encode_program(source: str, filename: str = "input.ja") -> EncodeResult:
    """Parse and encode a Janus-0 source program."""
    pp = preprocess_text(filename, source)
    program = parse_program(filename, pp.text, pp.line_origins)
    encoder = Encoder()
    return encoder.encode_program(program)


def generate_janus(result: EncodeResult, interp_path: str = "modern_interpreter.ja") -> str:
    """Generate a Janus program that runs the encoded program via self-interpreter."""
    lines: list[str] = []
    lines.append(f'#include "{interp_path}"')
    lines.append("")
    lines.append("void main() {")
    lines.append("    VM vm;")
    lines.append("    int expected_pc;")
    lines.append("")

    # Initialize code array using new C-style syntax
    code_vals = ", ".join(map(str, result.code))
    lines.append(f"    vm.code += {{{code_vals}}};")

    # Initialize proc table: [offset, stmt_count, num_params, 0] per proc
    if result.procs:
        proc_vals = []
        for proc in result.procs:
            proc_vals.extend([proc.code_offset, proc.stmt_count, len(proc.param_names), 0])
        proc_str = ", ".join(map(str, proc_vals))
        lines.append(f"    vm.procs += {{{proc_str}}};")

    lines.append("")
    lines.append(f"    vm.pc += {result.main_code_offset};")
    lines.append(f"    vm.n += {result.main_stmt_count};")
    lines.append(f"    call exec_stmts(vm);")
    lines.append("")

    # Print store results
    for name, vs in result.var_map.items():
        if vs.size == 1:
            lines.append(f'    printf("{name} = %d\\n", vm.store[{vs.slot}]);')
        else:
            lines.append(f'    // {name}[{vs.size}] at vm.store[{vs.slot}..{vs.slot + vs.size - 1}]')

    lines.append("")

    # Uncall to demonstrate reversibility
    lines.append(f"    uncall exec_stmts(vm);")
    lines.append(f"    // After uncall, store should be all zeros")
    lines.append(f"    expected_pc += {result.main_code_offset};")
    lines.append('    printf("After uncall, vm.pc = %d (should be %d)\\n", vm.pc, expected_pc);')

    lines.append("}")
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python3 -m jana_py.encode <file.ja>", file=sys.stderr)
        sys.exit(1)
    with open(sys.argv[1]) as f:
        source = f.read()
    result = encode_program(source, sys.argv[1])
    print(generate_janus(result))
