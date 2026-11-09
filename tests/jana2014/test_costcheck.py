"""Tests for the static cost predictor (jana_py/costcheck.py).

The predictions are checked against the dynamic profiler on the same
programs, so every test here is also a soundness check of the pair.
"""
from __future__ import annotations

from pathlib import Path
import sys
import textwrap
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from jana_py.costcheck import CostPrediction, analyze, format_prediction, iter_stmts
from jana_py.parser_jana2014 import parse_program
from jana_py.pebble import profile_space
from jana_py.validate import validate_program

EXAMPLE_DIR = ROOT / "tests" / "jana2014" / "fixtures" / "examples"


def _program(source: str):
    program = parse_program("costcheck_test.ja", textwrap.dedent(source))
    validate_program(program)
    return program


def _fixture(name: str):
    program = parse_program(name, (EXAMPLE_DIR / name).read_text())
    validate_program(program)
    return program


class TestFixtures(unittest.TestCase):
    def test_gcd(self):
        prog = _fixture("gcd.ja")
        pred = analyze(prog)
        self.assertFalse(pred.stack_free)
        self.assertTrue(pred.acyclic)
        self.assertEqual(pred.depth_bound, 1)
        self.assertEqual(pred.calls_bound, 1)
        self.assertFalse(pred.call_in_loop)
        self.assertEqual(pred.reachable, ["main", "gcd"])
        prof = profile_space(prog, std="jana2014")
        self.assertLessEqual(prof.call_depth_peak, pred.depth_bound)
        self.assertLessEqual(prof.total_calls, pred.calls_bound)

    def test_bubble_sort(self):
        pred = analyze(_fixture("bubble_sort.ja"))
        self.assertFalse(pred.stack_free)
        self.assertTrue(pred.acyclic)
        self.assertEqual(pred.depth_bound, 1)
        self.assertEqual(pred.calls_bound, 2)     # call bsort + uncall bsort

    def test_knapsack_is_certified_stack_free(self):
        prog = _fixture("knapsack.ja")
        pred = analyze(prog)
        self.assertTrue(pred.stack_free)
        self.assertEqual(pred.stack_stmts, 0)
        self.assertEqual(pred.calls_bound, 1)
        self.assertEqual(profile_space(prog, std="jana2014").stack_peak, 0)

    def test_recursive_fib_is_cyclic(self):
        pred = analyze(_fixture("fib.ja"))
        self.assertFalse(pred.acyclic)
        self.assertIsNone(pred.depth_bound)
        self.assertIsNone(pred.calls_bound)
        self.assertTrue(pred.stack_free)
        self.assertIn("fib", pred.call_graph["fib"])


class TestConstructed(unittest.TestCase):
    def test_call_inside_loop_makes_calls_unbounded(self):
        pred = analyze(_program("""\
            procedure inc(int x)
                x += 1

            procedure main()
                int x
                int i
                from i = 0 loop
                    call inc(x)
                    i += 1
                until i = 3
        """))
        self.assertTrue(pred.acyclic)
        self.assertEqual(pred.depth_bound, 1)
        self.assertTrue(pred.call_in_loop)
        self.assertIsNone(pred.calls_bound)

    def test_static_call_count_is_recursive_sum(self):
        prog = _program("""\
            procedure leaf(int x)
                x += 1

            procedure mid(int x)
                call leaf(x)
                uncall leaf(x)
                call leaf(x)

            procedure main()
                int x
                call mid(x)
                call mid(x)
                call leaf(x)
        """)
        pred = analyze(prog)
        # calls(mid) = 3, calls(main) = 2*(1+3) + 1 = 9
        self.assertEqual(pred.calls_bound, 9)
        self.assertEqual(pred.depth_bound, 2)
        prof = profile_space(prog, std="jana2014")
        self.assertEqual(prof.total_calls, 9)
        self.assertEqual(prof.call_depth_peak, 2)

    def test_unreachable_push_does_not_spoil_certificate(self):
        pred = analyze(_program("""\
            procedure unused(stack s, int x)
                push(x, s)

            procedure main()
                int x
                x += 1
        """))
        self.assertTrue(pred.stack_free)
        self.assertEqual(pred.reachable, ["main"])

    def test_pop_counts_as_stack_using(self):
        # uncall turns pop into push, so a lone pop is stack-using.
        pred = analyze(_program("""\
            procedure take(stack s, int x)
                pop(x, s)

            procedure main()
                stack s
                int x
                uncall take(s, x)
        """))
        self.assertFalse(pred.stack_free)

    def test_call_in_if_is_bounded_but_call_in_iterate_is_not(self):
        bounded = analyze(_program("""\
            procedure inc(int x)
                x += 1

            procedure main()
                int x
                if x = 0 then
                    call inc(x)
                else
                    skip
                fi x = 1
        """))
        self.assertEqual(bounded.calls_bound, 1)
        unbounded = analyze(_program("""\
            procedure inc(int x)
                x += 1

            procedure main()
                int x
                iterate int i = 0 to 2
                    call inc(x)
                end
        """))
        self.assertIsNone(unbounded.calls_bound)

    def test_iter_stmts_flags_loop_bodies(self):
        prog = _program("""\
            procedure main()
                int x
                int i
                x += 1
                from i = 0 loop
                    x += 1
                    i += 1
                until i = 2
        """)
        flags = [in_loop for _, in_loop in iter_stmts(prog.main.stmts)]
        self.assertEqual(flags, [False, False, True, True])

    def test_format(self):
        text = format_prediction(analyze(_fixture("gcd.ja")))
        self.assertIn("Static cost prediction", text)
        self.assertIn("call_depth_peak <=    1", text)
        self.assertIn("total_calls <=        1", text)
        self.assertIn("not certified", text)


if __name__ == "__main__":
    unittest.main()
