"""Tests for reversible circuit synthesis from Jana programs.

Tests cover:
  1. Simple XOR: x ^= y -> one CNOT gate
  2. Swap: x <=> y -> SWAP gate
  3. Addition: x += y -> adder circuit
  4. If-then: verify controlled gates
  5. Simulate a small circuit and compare with Runtime output
  6. Gate count / depth statistics
"""
from __future__ import annotations

import copy
import sys
import textwrap
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from jana_py.ast import (
    AssignStmt,
    BinExpr,
    BinOpKind,
    Ident,
    Lval,
    LvalExpr,
    ModOp,
    Number,
    SkipStmt,
    SourcePos,
    SwapStmt,
)
from jana_py.circuit import (
    Circuit,
    CircuitError,
    Gate,
    GateType,
    synthesize_program,
    synthesize_stmts,
)
from jana_py.parser import parse_program
from jana_py.runtime import Runtime
from jana_py.validate import validate_program


# Helper to quickly build a position
_POS = SourcePos("test", 1, 1)


def _run_program(source: str) -> dict[str, int]:
    """Run a Jana program and return the final variable store as {name: value}."""
    program = parse_program("test.ja", textwrap.dedent(source))
    validate_program(program)
    rt = Runtime(program)
    rt.run()
    assert rt._root_frame is not None
    return {k: copy.deepcopy(c.value) for k, c in rt._root_frame.vars.items()}


def _synthesize_source(source: str) -> Circuit:
    """Parse a Jana program and synthesize a circuit from it."""
    program = parse_program("test.ja", textwrap.dedent(source))
    validate_program(program)
    return synthesize_program(program)


class TestSimpleXOR(unittest.TestCase):
    """Test 1: x ^= y -> one CNOT gate."""

    def test_xor_produces_cnot(self):
        """x ^= y should produce exactly one CNOT gate."""
        source = """\
        procedure main()
            int x = 3
            int y = 5
            x ^= y
        """
        circuit = _synthesize_source(source)
        self.assertEqual(circuit.gate_count(), 1)
        gate = circuit.gates[0]
        self.assertEqual(gate.gate_type, GateType.CNOT)
        self.assertEqual(gate.controls, ["y"])
        self.assertEqual(gate.targets, ["x"])

    def test_xor_with_and_produces_toffoli(self):
        """x ^= y & z should produce exactly one Toffoli gate."""
        source = """\
        procedure main()
            int x = 0
            int y = 1
            int z = 1
            x ^= y & z
        """
        circuit = _synthesize_source(source)
        self.assertEqual(circuit.gate_count(), 1)
        gate = circuit.gates[0]
        self.assertEqual(gate.gate_type, GateType.TOFFOLI)
        self.assertEqual(gate.controls, ["y", "z"])
        self.assertEqual(gate.targets, ["x"])

    def test_xor_with_zero_no_gate(self):
        """x ^= 0 should produce no gates (identity)."""
        source = """\
        procedure main()
            int x = 5
            x ^= 0
        """
        circuit = _synthesize_source(source)
        self.assertEqual(circuit.gate_count(), 0)

    def test_xor_with_constant(self):
        """x ^= 7 should produce a CNOT gate with value."""
        source = """\
        procedure main()
            int x = 5
            x ^= 7
        """
        circuit = _synthesize_source(source)
        self.assertEqual(circuit.gate_count(), 1)
        gate = circuit.gates[0]
        self.assertEqual(gate.gate_type, GateType.CNOT)
        self.assertEqual(gate.targets, ["x"])
        self.assertEqual(gate.value, 7)


class TestSwap(unittest.TestCase):
    """Test 2: x <=> y -> SWAP gate."""

    def test_swap_produces_swap_gate(self):
        """x <=> y should produce exactly one SWAP gate."""
        source = """\
        procedure main()
            int x = 3
            int y = 7
            x <=> y
        """
        circuit = _synthesize_source(source)
        self.assertEqual(circuit.gate_count(), 1)
        gate = circuit.gates[0]
        self.assertEqual(gate.gate_type, GateType.SWAP)
        self.assertEqual(set(gate.targets), {"x", "y"})

    def test_swap_wires_registered(self):
        """Both wires should be registered in the circuit."""
        source = """\
        procedure main()
            int x = 1
            int y = 2
            x <=> y
        """
        circuit = _synthesize_source(source)
        self.assertIn("x", circuit.wires)
        self.assertIn("y", circuit.wires)


class TestAddition(unittest.TestCase):
    """Test 3: x += y -> adder circuit."""

    def test_add_variable_produces_add_gate(self):
        """x += y should produce an ADD gate."""
        source = """\
        procedure main()
            int x = 3
            int y = 5
            x += y
        """
        circuit = _synthesize_source(source)
        self.assertEqual(circuit.gate_count(), 1)
        gate = circuit.gates[0]
        self.assertEqual(gate.gate_type, GateType.ADD)
        self.assertEqual(gate.controls, ["y"])
        self.assertEqual(gate.targets, ["x"])

    def test_add_constant_produces_add_const(self):
        """x += 10 should produce an ADD_CONST gate."""
        source = """\
        procedure main()
            int x = 3
            x += 10
        """
        circuit = _synthesize_source(source)
        self.assertEqual(circuit.gate_count(), 1)
        gate = circuit.gates[0]
        self.assertEqual(gate.gate_type, GateType.ADD_CONST)
        self.assertEqual(gate.targets, ["x"])
        self.assertEqual(gate.value, 10)

    def test_sub_variable_produces_sub_gate(self):
        """x -= y should produce a SUB gate."""
        source = """\
        procedure main()
            int x = 10
            int y = 3
            x -= y
        """
        circuit = _synthesize_source(source)
        self.assertEqual(circuit.gate_count(), 1)
        gate = circuit.gates[0]
        self.assertEqual(gate.gate_type, GateType.SUB)
        self.assertEqual(gate.controls, ["y"])
        self.assertEqual(gate.targets, ["x"])

    def test_sub_constant_produces_sub_const(self):
        """x -= 5 should produce a SUB_CONST gate."""
        source = """\
        procedure main()
            int x = 10
            x -= 5
        """
        circuit = _synthesize_source(source)
        self.assertEqual(circuit.gate_count(), 1)
        gate = circuit.gates[0]
        self.assertEqual(gate.gate_type, GateType.SUB_CONST)
        self.assertEqual(gate.targets, ["x"])
        self.assertEqual(gate.value, 5)

    def test_add_zero_no_gate(self):
        """x += 0 should produce no gates."""
        source = """\
        procedure main()
            int x = 5
            x += 0
        """
        circuit = _synthesize_source(source)
        self.assertEqual(circuit.gate_count(), 0)


class TestIfThen(unittest.TestCase):
    """Test 4: if-then-fi -> controlled gate block."""

    def test_if_with_body_gates(self):
        """if-then block should emit the body gates."""
        source = """\
        procedure main()
            int x = 0
            int y = 1
            if y then
                x ^= y
            fi y
        """
        circuit = _synthesize_source(source)
        # The if-body produces one CNOT
        self.assertEqual(circuit.gate_count(), 1)
        gate = circuit.gates[0]
        self.assertEqual(gate.gate_type, GateType.CNOT)
        self.assertEqual(gate.controls, ["y"])
        self.assertEqual(gate.targets, ["x"])

    def test_if_else_produces_both_branches(self):
        """if-then-else-fi should emit gates from both branches."""
        source = """\
        procedure main()
            int x = 0
            int y = 1
            int z = 2
            if y then
                x ^= y
            else
                x ^= z
            fi y
        """
        circuit = _synthesize_source(source)
        self.assertEqual(circuit.gate_count(), 2)
        self.assertEqual(circuit.gates[0].gate_type, GateType.CNOT)
        self.assertEqual(circuit.gates[0].controls, ["y"])
        self.assertEqual(circuit.gates[1].gate_type, GateType.CNOT)
        self.assertEqual(circuit.gates[1].controls, ["z"])

    def test_if_with_multiple_stmts(self):
        """if block with multiple statements should produce multiple gates."""
        source = """\
        procedure main()
            int x = 0
            int y = 1
            int z = 2
            if y then
                x ^= y
                x += z
            fi y
        """
        circuit = _synthesize_source(source)
        self.assertEqual(circuit.gate_count(), 2)
        self.assertEqual(circuit.gates[0].gate_type, GateType.CNOT)
        self.assertEqual(circuit.gates[1].gate_type, GateType.ADD)


class TestSimulation(unittest.TestCase):
    """Test 5: Simulate circuits and compare with Runtime output."""

    def test_xor_simulation_matches_runtime(self):
        """Circuit simulation of x ^= y should match runtime."""
        source = """\
        procedure main()
            int x = 3
            int y = 5
            x ^= y
        """
        runtime_result = _run_program(source)
        circuit = _synthesize_source(source)
        sim_result = circuit.simulate({"x": 3, "y": 5})

        self.assertEqual(sim_result["x"], runtime_result["x"])
        self.assertEqual(sim_result["y"], runtime_result["y"])

    def test_swap_simulation_matches_runtime(self):
        """Circuit simulation of x <=> y should match runtime."""
        source = """\
        procedure main()
            int x = 3
            int y = 7
            x <=> y
        """
        runtime_result = _run_program(source)
        circuit = _synthesize_source(source)
        sim_result = circuit.simulate({"x": 3, "y": 7})

        self.assertEqual(sim_result["x"], runtime_result["x"])
        self.assertEqual(sim_result["y"], runtime_result["y"])

    def test_add_simulation_matches_runtime(self):
        """Circuit simulation of x += y should match runtime."""
        source = """\
        procedure main()
            int x = 3
            int y = 5
            x += y
        """
        runtime_result = _run_program(source)
        circuit = _synthesize_source(source)
        sim_result = circuit.simulate({"x": 3, "y": 5})

        self.assertEqual(sim_result["x"], runtime_result["x"])
        self.assertEqual(sim_result["y"], runtime_result["y"])

    def test_sub_simulation_matches_runtime(self):
        """Circuit simulation of x -= y should match runtime."""
        source = """\
        procedure main()
            int x = 10
            int y = 3
            x -= y
        """
        runtime_result = _run_program(source)
        circuit = _synthesize_source(source)
        sim_result = circuit.simulate({"x": 10, "y": 3})

        self.assertEqual(sim_result["x"], runtime_result["x"])
        self.assertEqual(sim_result["y"], runtime_result["y"])

    def test_toffoli_simulation_matches_runtime(self):
        """Circuit simulation of x ^= y & z should match runtime."""
        source = """\
        procedure main()
            int x = 0
            int y = 3
            int z = 5
            x ^= y & z
        """
        runtime_result = _run_program(source)
        circuit = _synthesize_source(source)
        sim_result = circuit.simulate({"x": 0, "y": 3, "z": 5})

        self.assertEqual(sim_result["x"], runtime_result["x"])

    def test_multi_statement_simulation(self):
        """Multi-statement program: simulation matches runtime."""
        source = """\
        procedure main()
            int x = 0
            int y = 3
            int z = 5
            x += y
            x ^= z
            y <=> z
        """
        runtime_result = _run_program(source)
        circuit = _synthesize_source(source)
        sim_result = circuit.simulate({"x": 0, "y": 3, "z": 5})

        self.assertEqual(sim_result["x"], runtime_result["x"])
        self.assertEqual(sim_result["y"], runtime_result["y"])
        self.assertEqual(sim_result["z"], runtime_result["z"])

    def test_add_constant_simulation(self):
        """Circuit simulation of x += 10 should match runtime."""
        source = """\
        procedure main()
            int x = 7
            x += 10
        """
        runtime_result = _run_program(source)
        circuit = _synthesize_source(source)
        sim_result = circuit.simulate({"x": 7})

        self.assertEqual(sim_result["x"], runtime_result["x"])

    def test_inverse_circuit_restores_state(self):
        """Running a circuit followed by its inverse restores original state."""
        source = """\
        procedure main()
            int x = 0
            int y = 3
            int z = 5
            x += y
            x ^= z
            y <=> z
        """
        circuit = _synthesize_source(source)
        inv = circuit.inverse()

        inputs = {"x": 0, "y": 3, "z": 5}
        mid = circuit.simulate(inputs)
        restored = inv.simulate(mid)

        self.assertEqual(restored["x"], 0)
        self.assertEqual(restored["y"], 3)
        self.assertEqual(restored["z"], 5)


class TestGateCountDepth(unittest.TestCase):
    """Test 6: Gate count and depth statistics."""

    def test_empty_circuit(self):
        """Empty circuit has 0 gates and 0 depth."""
        source = """\
        procedure main()
            int x = 0
            skip
        """
        circuit = _synthesize_source(source)
        self.assertEqual(circuit.gate_count(), 0)
        self.assertEqual(circuit.depth(), 0)

    def test_single_gate_depth(self):
        """Single gate gives depth 1."""
        source = """\
        procedure main()
            int x = 0
            int y = 1
            x ^= y
        """
        circuit = _synthesize_source(source)
        self.assertEqual(circuit.gate_count(), 1)
        self.assertEqual(circuit.depth(), 1)

    def test_sequential_depth(self):
        """Gates on the same wire have depth equal to the number of gates."""
        source = """\
        procedure main()
            int x = 0
            int y = 1
            int z = 2
            x ^= y
            x ^= z
        """
        circuit = _synthesize_source(source)
        self.assertEqual(circuit.gate_count(), 2)
        # Both gates touch x, so depth is 2
        self.assertEqual(circuit.depth(), 2)

    def test_parallel_depth(self):
        """Gates on disjoint wires can be parallel (depth = 1 each)."""
        # Two independent operations: a ^= b, c ^= d
        # We build this from AST nodes directly to have disjoint wires
        stmts = [
            AssignStmt(
                ModOp.XOR_EQ,
                Lval(Ident("a", _POS)),
                LvalExpr(Lval(Ident("b", _POS)), _POS),
                _POS,
            ),
            AssignStmt(
                ModOp.XOR_EQ,
                Lval(Ident("c", _POS)),
                LvalExpr(Lval(Ident("d", _POS)), _POS),
                _POS,
            ),
        ]
        circuit = synthesize_stmts(stmts, wires={"a", "b", "c", "d"})
        self.assertEqual(circuit.gate_count(), 2)
        # Independent gates: a,b and c,d don't overlap -> depth 1
        self.assertEqual(circuit.depth(), 1)

    def test_wires_tracked(self):
        """All wires referenced in the program should be tracked."""
        source = """\
        procedure main()
            int a = 0
            int b = 1
            int c = 2
            a ^= b
            a += c
        """
        circuit = _synthesize_source(source)
        self.assertIn("a", circuit.wires)
        self.assertIn("b", circuit.wires)
        self.assertIn("c", circuit.wires)


class TestToText(unittest.TestCase):
    """Test the human-readable text output."""

    def test_text_output_contains_gate_info(self):
        """to_text() should contain gate type and wire info."""
        source = """\
        procedure main()
            int x = 0
            int y = 1
            x ^= y
            x <=> y
        """
        circuit = _synthesize_source(source)
        text = circuit.to_text()
        self.assertIn("CNOT", text)
        self.assertIn("SWAP", text)
        self.assertIn("2 gates", text)

    def test_text_output_for_toffoli(self):
        """to_text() should show Toffoli gate correctly."""
        source = """\
        procedure main()
            int x = 0
            int y = 1
            int z = 1
            x ^= y & z
        """
        circuit = _synthesize_source(source)
        text = circuit.to_text()
        self.assertIn("Toffoli", text)
        self.assertIn("y", text)
        self.assertIn("z", text)


class TestGateInverse(unittest.TestCase):
    """Test Gate.inverse() method."""

    def test_cnot_is_self_inverse(self):
        gate = Gate(GateType.CNOT, controls=["a"], targets=["b"])
        inv = gate.inverse()
        self.assertEqual(inv.gate_type, GateType.CNOT)

    def test_swap_is_self_inverse(self):
        gate = Gate(GateType.SWAP, targets=["a", "b"])
        inv = gate.inverse()
        self.assertEqual(inv.gate_type, GateType.SWAP)

    def test_add_inverses_to_sub(self):
        gate = Gate(GateType.ADD, controls=["y"], targets=["x"])
        inv = gate.inverse()
        self.assertEqual(inv.gate_type, GateType.SUB)

    def test_sub_inverses_to_add(self):
        gate = Gate(GateType.SUB, controls=["y"], targets=["x"])
        inv = gate.inverse()
        self.assertEqual(inv.gate_type, GateType.ADD)

    def test_add_const_inverses_to_sub_const(self):
        gate = Gate(GateType.ADD_CONST, targets=["x"], value=5)
        inv = gate.inverse()
        self.assertEqual(inv.gate_type, GateType.SUB_CONST)
        self.assertEqual(inv.value, 5)

    def test_sub_const_inverses_to_add_const(self):
        gate = Gate(GateType.SUB_CONST, targets=["x"], value=3)
        inv = gate.inverse()
        self.assertEqual(inv.gate_type, GateType.ADD_CONST)
        self.assertEqual(inv.value, 3)


class TestCircuitInverse(unittest.TestCase):
    """Test Circuit.inverse() method."""

    def test_inverse_reverses_gate_order(self):
        """Inverse circuit should have gates in reverse order."""
        source = """\
        procedure main()
            int x = 0
            int y = 3
            x += y
            x ^= y
        """
        circuit = _synthesize_source(source)
        inv = circuit.inverse()

        self.assertEqual(inv.gate_count(), 2)
        # First gate in inverse should be the inverse of the last gate
        self.assertEqual(inv.gates[0].gate_type, GateType.CNOT)  # x ^= y is self-inverse
        self.assertEqual(inv.gates[1].gate_type, GateType.SUB)   # x += y -> x -= y

    def test_inverse_preserves_wires(self):
        source = """\
        procedure main()
            int x = 0
            int y = 3
            x += y
        """
        circuit = _synthesize_source(source)
        inv = circuit.inverse()
        self.assertEqual(circuit.wires, inv.wires)


class TestCircuitSimulateCNOTConst(unittest.TestCase):
    """Test simulation of CNOT with constant value (x ^= const)."""

    def test_xor_constant_simulation(self):
        """x ^= 7 should XOR the value."""
        source = """\
        procedure main()
            int x = 5
            x ^= 7
        """
        runtime_result = _run_program(source)
        circuit = _synthesize_source(source)
        sim_result = circuit.simulate({"x": 5})

        self.assertEqual(sim_result["x"], runtime_result["x"])
        self.assertEqual(sim_result["x"], 5 ^ 7)


class TestEdgeCases(unittest.TestCase):
    """Edge cases and error handling."""

    def test_no_main_raises_error(self):
        """Program without main should raise CircuitError."""
        from jana_py.ast import Program
        program = Program(main=None, procs=[])
        with self.assertRaises(CircuitError):
            synthesize_program(program)

    def test_skip_produces_no_gates(self):
        """skip statement should produce no gates."""
        stmts = [SkipStmt(_POS)]
        circuit = synthesize_stmts(stmts)
        self.assertEqual(circuit.gate_count(), 0)

    def test_from_loop_raises_error(self):
        """from-loop should raise CircuitError (not yet supported)."""
        source = """\
        procedure main()
            int x = 0
            from x = 0 do
                x += 1
            loop
                skip
            until x = 5
        """
        with self.assertRaises(CircuitError):
            _synthesize_source(source)


class TestFredkinGate(unittest.TestCase):
    """Test Fredkin gate simulation."""

    def test_fredkin_simulation_ctrl_true(self):
        """Fredkin gate with control=1 should swap targets."""
        circuit = Circuit(
            gates=[Gate(GateType.FREDKIN, controls=["c"], targets=["a", "b"])],
            wires={"c", "a", "b"},
        )
        result = circuit.simulate({"c": 1, "a": 3, "b": 7})
        self.assertEqual(result["a"], 7)
        self.assertEqual(result["b"], 3)

    def test_fredkin_simulation_ctrl_false(self):
        """Fredkin gate with control=0 should not swap targets."""
        circuit = Circuit(
            gates=[Gate(GateType.FREDKIN, controls=["c"], targets=["a", "b"])],
            wires={"c", "a", "b"},
        )
        result = circuit.simulate({"c": 0, "a": 3, "b": 7})
        self.assertEqual(result["a"], 3)
        self.assertEqual(result["b"], 7)


class TestNOTGate(unittest.TestCase):
    """Test NOT gate simulation."""

    def test_not_gate(self):
        """NOT gate should bitwise complement."""
        circuit = Circuit(
            gates=[Gate(GateType.NOT, targets=["x"])],
            wires={"x"},
        )
        result = circuit.simulate({"x": 0})
        self.assertEqual(result["x"], ~0)

    def test_not_not_is_identity(self):
        """Two NOT gates should be identity."""
        circuit = Circuit(
            gates=[
                Gate(GateType.NOT, targets=["x"]),
                Gate(GateType.NOT, targets=["x"]),
            ],
            wires={"x"},
        )
        result = circuit.simulate({"x": 42})
        self.assertEqual(result["x"], 42)


if __name__ == "__main__":
    unittest.main()
