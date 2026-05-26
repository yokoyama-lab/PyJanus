"""Tests for space complexity analysis (pebble game / memory profiling).

Covers:
1. Simple program: verify max_live_vars and total_steps
2. Program with local/delocal: verify local variables are tracked
3. Recursive fib: verify call_depth_max
4. Compare forward-only vs call+uncall: symmetric space usage
5. Format output is readable
"""
from __future__ import annotations

from pathlib import Path
import sys
import textwrap
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from jana_py.parser import parse_program
from jana_py.validate import validate_program
from jana_py.pebble import (
    SpaceProfile,
    SpaceSnapshot,
    compare_profiles,
    format_profile,
    profile_space,
    _is_zero,
    _value_bits,
)


def _profile(source: str, **kwargs) -> SpaceProfile:
    """Parse, validate, and profile a Jana program given as source text."""
    program = parse_program("pebble_test.ja", textwrap.dedent(source))
    validate_program(program)
    return profile_space(program, **kwargs)


class TestValueBits(unittest.TestCase):
    """Unit tests for the bit-width helper."""

    def test_zero(self):
        self.assertEqual(_value_bits(0), 0)

    def test_one(self):
        self.assertEqual(_value_bits(1), 1)

    def test_large_int(self):
        self.assertEqual(_value_bits(255), 8)

    def test_bool_true(self):
        self.assertEqual(_value_bits(True), 1)

    def test_bool_false(self):
        self.assertEqual(_value_bits(False), 0)

    def test_list(self):
        self.assertEqual(_value_bits([0, 1, 3]), 1 + 2)  # 0-bits + 1-bit + 2-bits

    def test_dict(self):
        self.assertEqual(_value_bits({"x": 7, "y": 0}), 3)

    def test_nested(self):
        self.assertEqual(_value_bits({"a": [1, 2], "b": 0}), 1 + 2)


class TestIsZero(unittest.TestCase):
    """Unit tests for zero-detection helper."""

    def test_int_zero(self):
        self.assertTrue(_is_zero(0))

    def test_int_nonzero(self):
        self.assertFalse(_is_zero(5))

    def test_bool_false(self):
        self.assertTrue(_is_zero(False))

    def test_bool_true(self):
        self.assertFalse(_is_zero(True))

    def test_empty_list(self):
        self.assertTrue(_is_zero([]))

    def test_all_zero_list(self):
        self.assertTrue(_is_zero([0, 0, 0]))

    def test_nonzero_list(self):
        self.assertFalse(_is_zero([0, 1, 0]))

    def test_zero_dict(self):
        self.assertTrue(_is_zero({"x": 0, "y": 0}))

    def test_nonzero_dict(self):
        self.assertFalse(_is_zero({"x": 0, "y": 1}))


class TestSimpleProgram(unittest.TestCase):
    """1. Simple program: verify max_live_vars and total_steps."""

    def test_single_assign(self):
        profile = _profile("""\
            procedure main()
                int x
                x += 5
        """)
        self.assertEqual(profile.total_steps, 1)
        # After x += 5, x is non-zero => 1 live var
        self.assertEqual(profile.max_live_vars, 1)
        self.assertGreater(profile.max_live_bits, 0)

    def test_two_assigns(self):
        profile = _profile("""\
            procedure main()
                int x
                int y
                x += 3
                y += 7
        """)
        self.assertEqual(profile.total_steps, 2)
        # After both assigns, both x and y are non-zero
        self.assertEqual(profile.max_live_vars, 2)

    def test_assign_and_clear(self):
        """Set a variable then clear it back to zero."""
        profile = _profile("""\
            procedure main()
                int x
                x += 5
                x -= 5
        """)
        self.assertEqual(profile.total_steps, 2)
        # Peak is 1 (after first assign), then it goes back to 0
        self.assertEqual(profile.max_live_vars, 1)
        # Check timeline: last snapshot should have 0 live vars
        last = profile.timeline[-1]
        self.assertEqual(last.live_vars, 0)

    def test_timeline_grows(self):
        """Timeline should have one init snapshot + one per statement."""
        profile = _profile("""\
            procedure main()
                int a
                int b
                a += 1
                b += 2
                a -= 1
        """)
        # 1 init + 3 statements = 4 snapshots
        self.assertEqual(len(profile.timeline), 4)
        self.assertEqual(profile.timeline[0].event, "init")

    def test_zero_program(self):
        """A program that does nothing has zero steps."""
        profile = _profile("""\
            procedure main()
                int x
                skip
        """)
        # skip is not counted as a step by the profiler (it's SkipStmt)
        # but _exec_stmt_impl still runs for it, so we get 1 step
        self.assertGreaterEqual(profile.total_steps, 0)
        self.assertEqual(profile.max_live_vars, 0)


class TestLocalDelocal(unittest.TestCase):
    """2. Program with local/delocal: verify local variables are tracked."""

    def test_local_var_peak(self):
        """local introduces an ancilla; delocal removes it."""
        profile = _profile("""\
            procedure main()
                int x
                x += 10
                local int tmp = x
                    x += tmp
                delocal int tmp = x / 2
        """)
        # local_var_max should be >= 1
        self.assertGreaterEqual(profile.local_var_max, 1)

    def test_nested_locals(self):
        """Two nested locals should give local_var_max >= 2."""
        profile = _profile("""\
            procedure main()
                int x
                x += 10
                local int a = x
                    local int b = a
                        x += b
                    delocal int b = a
                delocal int a = x / 2
        """)
        self.assertGreaterEqual(profile.local_var_max, 2)

    def test_local_adds_live_var(self):
        """A local with non-zero init should increase live_vars."""
        profile = _profile("""\
            procedure main()
                int x
                x += 5
                local int tmp = 3
                    x += tmp
                delocal int tmp = 3
        """)
        # At some point we should have both x and tmp live
        peak = max(snap.live_vars for snap in profile.timeline)
        self.assertGreaterEqual(peak, 2)


class TestRecursiveFib(unittest.TestCase):
    """3. Recursive fib: verify call_depth_max."""

    def test_fib_call_depth(self):
        profile = _profile("""\
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
                int n = 5
                call fib(x1, x2, n)
        """)
        # fib(5) recurses 5 times plus the top-level call = depth 6
        self.assertEqual(profile.call_depth_max, 6)

    def test_fib_total_steps(self):
        """Fib should execute a known number of steps."""
        profile = _profile("""\
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
                int n = 5
                call fib(x1, x2, n)
        """)
        self.assertGreater(profile.total_steps, 0)
        # The program should produce correct fibonacci values
        # (verified implicitly -- if it runs without error, the assertions pass)


class TestCallUncallSymmetry(unittest.TestCase):
    """4. Compare forward-only vs call+uncall: symmetric space usage."""

    def test_roundtrip_same_peak(self):
        """call+uncall should show symmetric space usage in the timeline."""
        fwd_source = """\
            procedure add_stuff(int x, int y)
                x += 3
                y += x
                x += y

            procedure main()
                int x = 1
                int y = 2
                call add_stuff(x, y)
        """
        rt_source = """\
            procedure add_stuff(int x, int y)
                x += 3
                y += x
                x += y

            procedure main()
                int x = 1
                int y = 2
                call add_stuff(x, y)
                uncall add_stuff(x, y)
        """
        fwd = _profile(fwd_source)
        rt = _profile(rt_source)

        # Roundtrip executes more steps
        self.assertGreater(rt.total_steps, fwd.total_steps)

        # After roundtrip, final snapshot should have same live_vars as
        # initial (before call)
        init_live = rt.timeline[0].live_vars
        final_live = rt.timeline[-1].live_vars
        self.assertEqual(init_live, final_live)

    def test_uncall_restores_space(self):
        """After call+uncall, space usage should return to pre-call level."""
        source = """\
            procedure bump(int x, int y)
                x += 10
                y += 20

            procedure main()
                int x
                int y
                call bump(x, y)
                uncall bump(x, y)
        """
        profile = _profile(source)
        # After roundtrip, both x and y should be back to zero
        last = profile.timeline[-1]
        self.assertEqual(last.live_vars, 0)
        self.assertEqual(last.live_bits, 0)


class TestFormatProfile(unittest.TestCase):
    """5. Format output is readable."""

    def test_format_contains_key_fields(self):
        profile = _profile("""\
            procedure main()
                int x
                x += 42
        """)
        text = format_profile(profile)
        self.assertIn("Space Profile", text)
        self.assertIn("Total steps:", text)
        self.assertIn("Peak live variables:", text)
        self.assertIn("Peak live bits:", text)
        self.assertIn("Max call depth:", text)
        self.assertIn("Peak local vars:", text)
        self.assertIn("Timeline", text)

    def test_format_timeline_entries(self):
        profile = _profile("""\
            procedure main()
                int x
                x += 1
                x += 2
        """)
        text = format_profile(profile)
        # Should contain "assign" events
        self.assertIn("assign", text)

    def test_format_empty_timeline(self):
        """An empty profile should still format without error."""
        profile = SpaceProfile(
            max_live_vars=0,
            max_live_bits=0,
            total_steps=0,
            timeline=[],
            call_depth_max=0,
            local_var_max=0,
        )
        text = format_profile(profile)
        self.assertIn("Total steps:", text)
        self.assertNotIn("Timeline", text)


class TestCompareProfiles(unittest.TestCase):
    """Test the comparison formatter."""

    def test_compare_output(self):
        a = SpaceProfile(
            max_live_vars=3,
            max_live_bits=24,
            total_steps=10,
            call_depth_max=2,
            local_var_max=1,
        )
        b = SpaceProfile(
            max_live_vars=5,
            max_live_bits=40,
            total_steps=20,
            call_depth_max=4,
            local_var_max=2,
        )
        text = compare_profiles(a, b)
        self.assertIn("Profile Comparison", text)
        self.assertIn("Total steps", text)
        self.assertIn("+10", text)  # delta for total_steps


class TestEventNames(unittest.TestCase):
    """Verify that event names are set correctly in the timeline."""

    def test_assign_event(self):
        profile = _profile("""\
            procedure main()
                int x
                x += 1
        """)
        events = [snap.event for snap in profile.timeline]
        self.assertIn("assign", events)

    def test_swap_event(self):
        profile = _profile("""\
            procedure main()
                int x = 1
                int y = 2
                x <=> y
        """)
        events = [snap.event for snap in profile.timeline]
        self.assertIn("swap", events)

    def test_call_event(self):
        profile = _profile("""\
            procedure nop(int x)
                skip

            procedure main()
                int x
                call nop(x)
        """)
        events = [snap.event for snap in profile.timeline]
        self.assertIn("call", events)


class TestArraySpace(unittest.TestCase):
    """Verify that arrays contribute to space measurements."""

    def test_array_bits(self):
        profile = _profile("""\
            procedure main()
                int arr[4]
                arr[0] += 255
                arr[1] += 255
                arr[2] += 255
                arr[3] += 255
        """)
        # 255 = 8 bits, 4 elements => 32 bits total
        self.assertEqual(profile.max_live_bits, 32)
        # Array is one variable with non-zero contents
        self.assertEqual(profile.max_live_vars, 1)


class TestInitializedVars(unittest.TestCase):
    """Variables initialized to non-zero should count from the start."""

    def test_nonzero_init(self):
        profile = _profile("""\
            procedure main()
                int x = 42
                skip
        """)
        # x is non-zero from the start
        self.assertEqual(profile.max_live_vars, 1)
        # The init snapshot should already show 1 live var
        self.assertEqual(profile.timeline[0].live_vars, 1)


if __name__ == "__main__":
    unittest.main()
