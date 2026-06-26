"""Tests for the program equivalence checker."""
from __future__ import annotations

import sys
import textwrap
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from jana_py.parser_jana2014 import parse_program
from jana_py.equiv import check_equivalence, check_inverse, check_self_inverse


def parse(source: str) -> "Program":
    return parse_program("test.ja", textwrap.dedent(source))


class TestEquivalentPrograms(unittest.TestCase):
    """Two programs that compute the same function should be equivalent."""

    def test_two_equivalent_fibonacci_implementations(self) -> None:
        """Two different ways to compute fib(n) iteratively should agree."""
        # Implementation A: standard iterative fib using a temp variable
        prog_a = parse("""\
            procedure fib(int x1, int x2, int n)
                if n = 0 then
                    x1 += 1
                    x2 += 1
                else
                    n -= 1
                    call fib(x1, x2, n)
                    x1 += x2
                    x1 <=> x2
                fi x1 = x2

            procedure main()
                int x1
                int x2
                int n = 3
                call fib(x1, x2, n)
        """)

        # Implementation B: same algorithm, but using += rewritten as
        # two separate additions through a local variable
        prog_b = parse("""\
            procedure fib(int x1, int x2, int n)
                if n = 0 then
                    x1 += 1
                    x2 += 1
                else
                    n -= 1
                    call fib(x1, x2, n)
                    local int tmp = x2
                        x1 += tmp
                    delocal int tmp = x2
                    x1 <=> x2
                fi x1 = x2

            procedure main()
                int x1
                int x2
                int n = 3
                call fib(x1, x2, n)
        """)

        result = check_equivalence(prog_a, prog_b, ["n"], input_range=range(0, 8))
        self.assertTrue(result.equivalent, f"Counterexample: {result.counterexample}")
        self.assertEqual(result.tested, 8)

    def test_double_inversion_is_identity(self) -> None:
        """A program inverted twice should be equivalent to the original."""
        from jana_py.invert import invert_stmts
        from dataclasses import replace

        prog = parse("""\
            procedure main()
                int a = 3
                int b = 5
                a += b
                b += a * 2
        """)

        # Invert the main body twice
        inv1 = invert_stmts(prog.main.stmts, global_mode=False)
        inv2 = invert_stmts(inv1, global_mode=False)
        prog_double_inv = replace(prog, main=replace(prog.main, stmts=inv2))

        result = check_equivalence(prog, prog_double_inv, ["a", "b"], input_range=range(-4, 5))
        self.assertTrue(result.equivalent, f"Counterexample: {result.counterexample}")
        self.assertGreater(result.tested, 0)


class TestNonEquivalentPrograms(unittest.TestCase):
    """A correct program vs a buggy version should produce a counterexample."""

    def test_correct_vs_buggy(self) -> None:
        """Changing += to -= should produce a counterexample."""
        correct = parse("""\
            procedure main()
                int x = 1
                int y
                y += x * 2
        """)

        buggy = parse("""\
            procedure main()
                int x = 1
                int y
                y -= x * 2
        """)

        result = check_equivalence(correct, buggy, ["x"], input_range=range(1, 5))
        self.assertFalse(result.equivalent)
        self.assertIsNotNone(result.counterexample)
        self.assertIsNotNone(result.diff)
        # The stores should differ
        store_a, store_b = result.diff
        self.assertNotEqual(store_a, store_b)


class TestCheckInverse(unittest.TestCase):
    """check_inverse verifies that prog; invert(prog) = identity."""

    def test_fib_inverse(self) -> None:
        """Fibonacci run forward then backward should be the identity."""
        prog = parse("""\
            procedure fib(int x1, int x2, int n)
                if n = 0 then
                    x1 += 1
                    x2 += 1
                else
                    n -= 1
                    call fib(x1, x2, n)
                    x1 += x2
                    x1 <=> x2
                fi x1 = x2

            procedure main()
                int x1
                int x2
                int n = 3
                call fib(x1, x2, n)
        """)

        result = check_inverse(prog, ["n"], input_range=range(0, 8))
        self.assertTrue(result.equivalent, f"Counterexample: {result.counterexample}")

    def test_simple_arithmetic_inverse(self) -> None:
        """Simple arithmetic reversed should restore initial values."""
        prog = parse("""\
            procedure main()
                int a = 1
                int b
                b += a * 3
                a += b
        """)

        result = check_inverse(prog, ["a"], input_range=range(-5, 6))
        self.assertTrue(result.equivalent, f"Counterexample: {result.counterexample}")


class TestCheckSelfInverse(unittest.TestCase):
    """check_self_inverse verifies that prog; prog = identity."""

    def test_swap_is_self_inverse(self) -> None:
        """Swapping two variables twice returns them to original values."""
        prog = parse("""\
            procedure main()
                int a = 1
                int b = 2
                a <=> b
        """)

        result = check_self_inverse(prog, ["a", "b"], input_range=range(-3, 4))
        self.assertTrue(result.equivalent, f"Counterexample: {result.counterexample}")

    def test_xor_swap_is_self_inverse(self) -> None:
        """XOR swap applied twice is the identity."""
        prog = parse("""\
            procedure main()
                int a = 1
                int b = 2
                a ^= b
                b ^= a
                a ^= b
        """)

        result = check_self_inverse(prog, ["a", "b"], input_range=range(-3, 4))
        self.assertTrue(result.equivalent, f"Counterexample: {result.counterexample}")

    def test_non_self_inverse_program(self) -> None:
        """An addition is not its own inverse (should fail)."""
        prog = parse("""\
            procedure main()
                int x = 1
                int y
                y += x
        """)

        result = check_self_inverse(prog, ["x"], input_range=range(1, 5))
        self.assertFalse(result.equivalent)
        self.assertIsNotNone(result.counterexample)
        self.assertIsNotNone(result.diff)


class TestEdgeCases(unittest.TestCase):
    """Edge cases for the equivalence checker."""

    def test_no_input_vars(self) -> None:
        """With no input variables to vary, a single test is run."""
        prog = parse("""\
            procedure main()
                int x
                x += 42
        """)

        result = check_equivalence(prog, prog, [])
        self.assertTrue(result.equivalent)
        self.assertEqual(result.tested, 1)

    def test_max_combinations_limit(self) -> None:
        """Safety limit should cap the number of tests."""
        prog = parse("""\
            procedure main()
                int a
                int b
                a += b
        """)

        result = check_equivalence(
            prog, prog, ["a", "b"],
            input_range=range(-100, 101),
            max_combinations=50,
        )
        self.assertTrue(result.equivalent)
        self.assertEqual(result.tested, 50)

    def test_runtime_error_during_execution_is_treated_as_a_distinct_store(self) -> None:
        """If one side raises (e.g. a failed assertion) it is store=None, so a
        program that aborts on some inputs is not equivalent to one that never
        does — the checker reports a counterexample instead of crashing."""
        # `if x = 0 ... fi x = 1` is a reversibility-violating assertion: when
        # x = 0 the entry branch runs but the exit assertion x = 1 fails.
        aborts = parse("""\
            procedure main()
                int x
                if x = 0 then
                    x += 0
                else
                    skip
                fi x = 1
        """)
        never = parse("""\
            procedure main()
                int x
                skip
        """)
        result = check_equivalence(aborts, never, ["x"], input_range=range(0, 3))
        self.assertFalse(result.equivalent)
        self.assertIsNotNone(result.counterexample)
        # the aborting side produced no store
        store_a, _ = result.diff
        self.assertIsNone(store_a)


class TestNoMainProcedure(unittest.TestCase):
    """The checker's helpers must reject programs that have no main."""

    def _mainless(self) -> "Program":
        from dataclasses import replace
        prog = parse("""\
            procedure main()
                int x
                x += 1
        """)
        return replace(prog, main=None)

    def test_set_input_values_passes_through_mainless_program(self) -> None:
        # _set_input_values short-circuits (it cannot bind inputs without a main).
        result = check_equivalence(self._mainless(), self._mainless(), [])
        # Two main-less programs both yield an empty store -> trivially equal.
        self.assertTrue(result.equivalent)

    def test_check_inverse_rejects_mainless(self) -> None:
        with self.assertRaises(ValueError):
            check_inverse(self._mainless(), ["x"])

    def test_check_self_inverse_rejects_mainless(self) -> None:
        with self.assertRaises(ValueError):
            check_self_inverse(self._mainless(), ["x"])


if __name__ == "__main__":
    unittest.main()
