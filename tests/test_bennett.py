"""Tests for Bennett's automatic reversibilization (compute-copy-uncompute).

Each test constructs a Jana program that uses the Bennett-embedded version
of an irreversible computation and verifies:
  - The output variable receives the correct computed value.
  - The input variable is preserved (not destroyed).
  - The transformation is reversible (call + uncall = identity).
"""
from __future__ import annotations

import copy
from pathlib import Path
import sys
import textwrap
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from jana_py.ast import (
    AssignStmt,
    BinExpr,
    BinOpKind,
    DeclType,
    Ident,
    IfStmt,
    IntType,
    Lval,
    LvalExpr,
    ModOp,
    Number,
    SourcePos,
    Type,
)
from jana_py.bennett import bennett_embed, bennett_embed_procedure, _collect_modified_vars
from jana_py.parser import parse_program
from jana_py.validate import validate_program
from jana_py.runtime import Runtime


# Helpers -------------------------------------------------------------------

_POS = SourcePos("<test>", 0, 0)


def _ident(name: str) -> Ident:
    return Ident(name=name, pos=_POS)


def _lval(name: str) -> Lval:
    return Lval(ident=_ident(name))


def _lval_expr(name: str) -> LvalExpr:
    return LvalExpr(lval=_lval(name), pos=_POS)


def _num(n: int) -> Number:
    return Number(value=n, pos=_POS)


def _int_type() -> Type:
    return Type(kind="int", pos=_POS, int_type=IntType.I32)


def run_and_get_store(source: str) -> dict[str, object]:
    """Parse, validate, and run a Jana program; return the final variable store."""
    program = parse_program("bennett_test.ja", textwrap.dedent(source))
    validate_program(program)
    rt = Runtime(program)
    rt.run()
    assert rt._root_frame is not None
    return {k: copy.deepcopy(c.value) for k, c in rt._root_frame.vars.items()}


# Tests ---------------------------------------------------------------------


class TestCollectModifiedVars(unittest.TestCase):
    """Test the helper that collects modified variables from statements."""

    def test_assign(self) -> None:
        stmts = [
            AssignStmt(ModOp.ADD_EQ, _lval("x"), _lval_expr("y"), _POS),
        ]
        self.assertEqual(_collect_modified_vars(stmts), {"x"})

    def test_multiple_assigns(self) -> None:
        stmts = [
            AssignStmt(ModOp.ADD_EQ, _lval("x"), _lval_expr("y"), _POS),
            AssignStmt(ModOp.SUB_EQ, _lval("y"), _num(1), _POS),
        ]
        self.assertEqual(_collect_modified_vars(stmts), {"x", "y"})


class TestBennettEmbedAST(unittest.TestCase):
    """Test that bennett_embed produces the expected AST structure."""

    def test_single_assign_produces_local_block(self) -> None:
        """x += y should produce a local block with ancilla anc__x."""
        stmts = [
            AssignStmt(ModOp.ADD_EQ, _lval("x"), _lval_expr("y"), _POS),
        ]
        result = bennett_embed(stmts, {"x": "out"})
        # Result should be a list with one LocalStmt
        self.assertEqual(len(result), 1)
        from jana_py.ast import LocalStmt
        self.assertIsInstance(result[0], LocalStmt)
        local = result[0]
        self.assertEqual(local.enter_decl.ident.name, "anc__x")

    def test_output_map_creates_xor_copy(self) -> None:
        """The copy phase should use ^= to copy from ancilla to output."""
        stmts = [
            AssignStmt(ModOp.ADD_EQ, _lval("x"), _lval_expr("y"), _POS),
        ]
        result = bennett_embed(stmts, {"x": "out"})
        from jana_py.ast import LocalStmt
        # Dig into the LocalStmt body
        body = result[0].body
        # Body should have: forward (1 stmt) + copy (1 stmt) + uncompute (1 stmt) = 3
        self.assertEqual(len(body), 3)
        # The copy statement should be XOR
        copy_stmt = body[1]
        self.assertIsInstance(copy_stmt, AssignStmt)
        self.assertEqual(copy_stmt.mod_op, ModOp.XOR_EQ)
        self.assertEqual(copy_stmt.lval.ident.name, "out")


class TestBennettSimpleArithmetic(unittest.TestCase):
    """Test Bennett embedding with a simple arithmetic computation via the runtime."""

    def test_double_preserves_input(self) -> None:
        """Bennett-embed 'x += y * 2': input y should be preserved, result in out."""
        # We build a full Jana program that manually implements the Bennett pattern.
        # The forward computation is: x += y * 2
        # After Bennett embedding: out gets the value y*2, y is unchanged.
        source = """\
        procedure main()
            int y = 5
            int out
            local int anc__x = 0
                anc__x += y * 2
                out ^= anc__x
                anc__x -= y * 2
            delocal int anc__x = 0
        """
        store = run_and_get_store(source)
        self.assertEqual(store["y"], 5, "input y should be preserved")
        self.assertEqual(store["out"], 10, "out should be y*2 = 10")

    def test_add_with_multiple_steps(self) -> None:
        """Bennett-embed multi-step: x += y; x += z."""
        source = """\
        procedure main()
            int y = 3
            int z = 7
            int out
            local int anc__x = 0
                anc__x += y
                anc__x += z
                out ^= anc__x
                anc__x -= z
                anc__x -= y
            delocal int anc__x = 0
        """
        store = run_and_get_store(source)
        self.assertEqual(store["y"], 3)
        self.assertEqual(store["z"], 7)
        self.assertEqual(store["out"], 10)


class TestBennettWithIfElse(unittest.TestCase):
    """Bennett embedding with conditional logic."""

    def test_if_else_flag_one(self) -> None:
        """Conditional computation embedded with Bennett's trick, flag=1 branch."""
        # Forward computation:
        #   if flag = 1 then x += 10 else x += 20 fi flag = 1
        # Bennett-embedded: ancilla anc__x, anc__flag
        # Since flag is read in conditions but also might be considered modified
        # by the if structure, we use the simplest form: only x is modified.
        source = """\
        procedure main()
            int flag = 1
            int out
            local int anc__x = 0
                if flag = 1 then
                    anc__x += 10
                else
                    anc__x += 20
                fi flag = 1
                out ^= anc__x
                if flag = 1 then
                    anc__x -= 10
                else
                    anc__x -= 20
                fi flag = 1
            delocal int anc__x = 0
        """
        store = run_and_get_store(source)
        self.assertEqual(store["flag"], 1, "flag should be preserved")
        self.assertEqual(store["out"], 10, "out should be 10 (then-branch)")

    def test_if_else_flag_zero(self) -> None:
        """Same structure but flag=0 takes else branch."""
        source = """\
        procedure main()
            int flag = 0
            int out
            local int anc__x = 0
                if flag = 0 then
                    anc__x += 100
                else
                    anc__x += 200
                fi flag = 0
                out ^= anc__x
                if flag = 0 then
                    anc__x -= 100
                else
                    anc__x -= 200
                fi flag = 0
            delocal int anc__x = 0
        """
        store = run_and_get_store(source)
        self.assertEqual(store["flag"], 0)
        self.assertEqual(store["out"], 100)


class TestBennettReversibility(unittest.TestCase):
    """Verify that Bennett-embedded computations are truly reversible:
    call + uncall = identity."""

    def _assert_call_uncall_identity(self, proc_body: str, main_vars: str, call_args: str) -> None:
        """Assert that calling and uncalling a procedure restores original state."""
        # Program with call + uncall
        rt_source = f"""\
        procedure compute({call_args})
            {proc_body}

        procedure main()
            {main_vars}
            call compute({', '.join(v.split()[-1].rstrip(',') for v in call_args.split(','))})
            uncall compute({', '.join(v.split()[-1].rstrip(',') for v in call_args.split(','))})
        """
        # Initial state (no calls)
        init_source = f"""\
        procedure compute({call_args})
            {proc_body}

        procedure main()
            {main_vars}
            skip
        """
        rt_store = run_and_get_store(rt_source)
        init_store = run_and_get_store(init_source)
        self.assertEqual(rt_store, init_store, "call+uncall did not restore initial state")

    def test_bennett_embedded_is_reversible(self) -> None:
        """A Bennett-embedded procedure should be inherently reversible."""
        # The procedure uses local/delocal (Bennett pattern) to compute x += y
        # and copy the result to out via XOR.
        proc_body = textwrap.dedent("""\
            local int anc0 = 0
                anc0 += x
                out ^= anc0
                anc0 -= x
            delocal int anc0 = 0""")
        self._assert_call_uncall_identity(
            proc_body,
            "int x = 7\n    int out",
            "int x, int out",
        )

    def test_bennett_multi_step_reversible(self) -> None:
        """Multi-step Bennett-embedded computation is reversible."""
        proc_body = textwrap.dedent("""\
            local int anc0 = 0
                anc0 += a
                anc0 += b
                out ^= anc0
                anc0 -= b
                anc0 -= a
            delocal int anc0 = 0""")
        self._assert_call_uncall_identity(
            proc_body,
            "int a = 3\n    int b = 4\n    int out",
            "int a, int b, int out",
        )

    def test_bennett_if_else_reversible(self) -> None:
        """Bennett-embedded conditional computation is reversible."""
        proc_body = textwrap.dedent("""\
            local int anc0 = 0
                if flag = 1 then
                    anc0 += 10
                else
                    anc0 += 20
                fi flag = 1
                out ^= anc0
                if flag = 1 then
                    anc0 -= 10
                else
                    anc0 -= 20
                fi flag = 1
            delocal int anc0 = 0""")
        self._assert_call_uncall_identity(
            proc_body,
            "int flag = 1\n    int out",
            "int flag, int out",
        )


class TestBennettEmbedEndToEnd(unittest.TestCase):
    """End-to-end: use bennett_embed() to transform AST, build a program,
    and verify it runs correctly."""

    def test_embed_and_run_simple(self) -> None:
        """Use bennett_embed on [x += y] and verify the result runs correctly."""
        from jana_py.ast import (
            LocalStmt, ProcMain, Program, Vdecl,
        )
        from jana_py.bennett import bennett_embed

        # Original irreversible computation: x += y
        fwd_stmts = [
            AssignStmt(ModOp.ADD_EQ, _lval("x"), _lval_expr("y"), _POS),
        ]

        # Bennett-embed: we want the result in "out", computed from "x"
        embedded = bennett_embed(fwd_stmts, {"x": "out"})

        # Build a full program around the embedded block.
        vdecls = [
            Vdecl(DeclType.VARIABLE, _int_type(), _ident("y"), [], _num(5), _POS),
            Vdecl(DeclType.VARIABLE, _int_type(), _ident("out"), [], _num(0), _POS),
        ]
        main = ProcMain(vdecls=vdecls, stmts=embedded, pos=_POS)
        program = Program(main=main, procs=[])

        rt = Runtime(program)
        rt.run()
        store = {k: copy.deepcopy(c.value) for k, c in rt._root_frame.vars.items()}

        self.assertEqual(store["y"], 5, "input y should be preserved")
        self.assertEqual(store["out"], 5, "out should be y = 5 (since x starts at 0, x += y => 5)")

    def test_embed_and_run_multiply(self) -> None:
        """Bennett-embed [x += y * 3] and verify output."""
        from jana_py.ast import ProcMain, Program, Vdecl
        from jana_py.bennett import bennett_embed

        fwd_stmts = [
            AssignStmt(
                ModOp.ADD_EQ, _lval("x"),
                BinExpr(BinOpKind.MUL, _lval_expr("y"), _num(3), _POS),
                _POS,
            ),
        ]

        embedded = bennett_embed(fwd_stmts, {"x": "out"})

        vdecls = [
            Vdecl(DeclType.VARIABLE, _int_type(), _ident("y"), [], _num(4), _POS),
            Vdecl(DeclType.VARIABLE, _int_type(), _ident("out"), [], _num(0), _POS),
        ]
        main = ProcMain(vdecls=vdecls, stmts=embedded, pos=_POS)
        program = Program(main=main, procs=[])

        rt = Runtime(program)
        rt.run()
        store = {k: copy.deepcopy(c.value) for k, c in rt._root_frame.vars.items()}

        self.assertEqual(store["y"], 4, "input y preserved")
        self.assertEqual(store["out"], 12, "out = y * 3 = 12")

    def test_embed_two_modified_vars(self) -> None:
        """Bennett-embed [x += y; z += x * 2]: both x and z are modified."""
        from jana_py.ast import ProcMain, Program, Vdecl
        from jana_py.bennett import bennett_embed

        fwd_stmts = [
            AssignStmt(ModOp.ADD_EQ, _lval("x"), _lval_expr("y"), _POS),
            AssignStmt(
                ModOp.ADD_EQ, _lval("z"),
                BinExpr(BinOpKind.MUL, _lval_expr("x"), _num(2), _POS),
                _POS,
            ),
        ]

        # We want z's final value in "out_z"
        embedded = bennett_embed(fwd_stmts, {"z": "out_z"})

        vdecls = [
            Vdecl(DeclType.VARIABLE, _int_type(), _ident("y"), [], _num(5), _POS),
            Vdecl(DeclType.VARIABLE, _int_type(), _ident("out_z"), [], _num(0), _POS),
        ]
        main = ProcMain(vdecls=vdecls, stmts=embedded, pos=_POS)
        program = Program(main=main, procs=[])

        rt = Runtime(program)
        rt.run()
        store = {k: copy.deepcopy(c.value) for k, c in rt._root_frame.vars.items()}

        # Forward: x starts 0, x += y => x=5, z starts 0, z += x*2 => z=10
        self.assertEqual(store["y"], 5, "input y preserved")
        self.assertEqual(store["out_z"], 10, "out_z = (0 + y) * 2 = 10")


if __name__ == "__main__":
    unittest.main()
