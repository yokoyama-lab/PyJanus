"""Tests for the inverse interpreter (output -> input inference)."""
from __future__ import annotations

from pathlib import Path
import sys
import textwrap
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from jana_py.inverse import InverseResult, find_input, run_inverse, run_inverse_from_source, verify_inverse
from jana_py.parser import parse_program
from jana_py.validate import validate_program


class TestRunInverse(unittest.TestCase):
  """Test run_inverse and run_inverse_from_source."""

  def test_simple_add(self) -> None:
    """x += 5 with final x=5 -> initial x=0."""
    source = textwrap.dedent("""\
      procedure main()
          int x
          x += 5
    """)
    result = run_inverse_from_source(source, {"x": 5})
    self.assertTrue(result.success, result.error)
    self.assertEqual(result.initial_store["x"], 0)

  def test_simple_sub(self) -> None:
    """x -= 3 with final x=7 -> initial x=10."""
    source = textwrap.dedent("""\
      procedure main()
          int x
          x -= 3
    """)
    result = run_inverse_from_source(source, {"x": 7})
    self.assertTrue(result.success, result.error)
    self.assertEqual(result.initial_store["x"], 10)

  def test_multi_variable(self) -> None:
    """Given final store for multiple variables, recover all initial values."""
    source = textwrap.dedent("""\
      procedure main()
          int x
          int y
          x += 3
          y += x
          x += y
    """)
    # Forward: x=0,y=0 -> x+=3 -> x=3,y=0 -> y+=x -> x=3,y=3 -> x+=y -> x=6,y=3
    result = run_inverse_from_source(source, {"x": 6, "y": 3})
    self.assertTrue(result.success, result.error)
    self.assertEqual(result.initial_store["x"], 0)
    self.assertEqual(result.initial_store["y"], 0)

  def test_xor_assign(self) -> None:
    """x ^= 0xFF with final x=0xFF -> initial x=0."""
    source = textwrap.dedent("""\
      procedure main()
          int x
          x ^= 255
    """)
    result = run_inverse_from_source(source, {"x": 255})
    self.assertTrue(result.success, result.error)
    self.assertEqual(result.initial_store["x"], 0)

  def test_swap(self) -> None:
    """a <=> b with final a=5,b=3 -> initial a=3,b=5."""
    source = textwrap.dedent("""\
      procedure main()
          int a
          int b
          a += 3
          b += 5
          a <=> b
    """)
    # Forward: a=0,b=0 -> a=3,b=5 -> swap -> a=5,b=3
    result = run_inverse_from_source(source, {"a": 5, "b": 3})
    self.assertTrue(result.success, result.error)
    self.assertEqual(result.initial_store["a"], 0)
    self.assertEqual(result.initial_store["b"], 0)

  def test_with_initial_values(self) -> None:
    """Program with non-zero initial values."""
    source = textwrap.dedent("""\
      procedure main()
          int x = 10
          int y
          y += x
          x += y
    """)
    # Forward: x=10, y=0 -> y+=x -> y=10 -> x+=y -> x=20
    result = run_inverse_from_source(source, {"x": 20, "y": 10})
    self.assertTrue(result.success, result.error)
    self.assertEqual(result.initial_store["x"], 10)
    self.assertEqual(result.initial_store["y"], 0)


class TestFibonacciInverse(unittest.TestCase):
  """Test inverse interpreter with Fibonacci programs."""

  FIB_SOURCE = textwrap.dedent("""\
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

  def test_fib_inverse_recovers_n(self) -> None:
    """Given final fib values, recover initial n=5 (rest 0)."""
    # Forward: n=5 (init) -> fib(0,0,5) produces x1=8, x2=13, n=0
    result = run_inverse_from_source(
      self.FIB_SOURCE,
      {"x1": 8, "x2": 13, "n": 0},
    )
    self.assertTrue(result.success, result.error)
    self.assertEqual(result.initial_store["x1"], 0)
    self.assertEqual(result.initial_store["x2"], 0)
    self.assertEqual(result.initial_store["n"], 5)

  def test_fib_inverse_n3(self) -> None:
    """Fibonacci for n=3."""
    source = textwrap.dedent("""\
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
    # fib(3): x1=3, x2=5, n=0
    result = run_inverse_from_source(source, {"x1": 3, "x2": 5, "n": 0})
    self.assertTrue(result.success, result.error)
    self.assertEqual(result.initial_store["n"], 3)
    self.assertEqual(result.initial_store["x1"], 0)
    self.assertEqual(result.initial_store["x2"], 0)


class TestVerification(unittest.TestCase):
  """Test that inverse results verify correctly when run forward."""

  def test_roundtrip_simple(self) -> None:
    """Run inverse, then verify by running forward."""
    source = textwrap.dedent("""\
      procedure main()
          int x
          int y
          x += 7
          y += x
    """)
    final = {"x": 7, "y": 7}

    program = parse_program("test.ja", source)
    validate_program(program)

    inv_result = run_inverse(program, final)
    self.assertTrue(inv_result.success, inv_result.error)

    verified = verify_inverse(program, inv_result.initial_store, final)
    self.assertTrue(verified, "Forward verification failed")

  def test_roundtrip_fib(self) -> None:
    """Inverse then forward verification for Fibonacci."""
    source = textwrap.dedent("""\
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
          int n
          n += 5
          call fib(x1, x2, n)
    """)
    final = {"x1": 8, "x2": 13, "n": 0}

    program = parse_program("test.ja", source)
    validate_program(program)

    inv_result = run_inverse(program, final)
    self.assertTrue(inv_result.success, inv_result.error)

    verified = verify_inverse(program, inv_result.initial_store, final)
    self.assertTrue(verified, "Forward verification failed for Fibonacci")

  def test_roundtrip_multi_step(self) -> None:
    """Multiple operations, verify roundtrip."""
    source = textwrap.dedent("""\
      procedure main()
          int a
          int b
          int c
          a += 1
          b += 2
          c += a + b
          a += c
    """)
    # Forward: a=0,b=0,c=0 -> a=1 -> b=2 -> c=3 -> a=4
    final = {"a": 4, "b": 2, "c": 3}

    program = parse_program("test.ja", source)
    validate_program(program)

    inv_result = run_inverse(program, final)
    self.assertTrue(inv_result.success, inv_result.error)

    verified = verify_inverse(program, inv_result.initial_store, final)
    self.assertTrue(verified)


class TestFindInput(unittest.TestCase):
  """Test the brute-force find_input search."""

  def test_find_n_for_fib_13(self) -> None:
    """Search for n that gives fib(n) = 13 (x2=13)."""
    source = textwrap.dedent("""\
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
          int n
          call fib(x1, x2, n)
    """)
    program = parse_program("test.ja", source)
    validate_program(program)

    # fib(n=5) gives x2=13 (with n initialized by search)
    result = find_input(
      program,
      output_var="x2",
      target_value=13,
      free_vars=["n"],
      search_range=range(0, 15),
    )
    self.assertIsNotNone(result)
    # n=5 gives the pair (8, 13), so x2=13 at n=5
    # But the main does NOT do n += 5, it uses the search value directly
    # fib(0,0,n): n=5 -> x2=13
    self.assertEqual(result["n"], 5)

  def test_find_input_simple(self) -> None:
    """Search for x that gives y=15 in y += x + 5."""
    source = textwrap.dedent("""\
      procedure main()
          int x
          int y
          y += x + 5
    """)
    program = parse_program("test.ja", source)
    validate_program(program)

    result = find_input(
      program,
      output_var="y",
      target_value=15,
      free_vars=["x"],
      search_range=range(0, 20),
    )
    self.assertIsNotNone(result)
    self.assertEqual(result["x"], 10)

  def test_find_input_no_solution(self) -> None:
    """No solution exists within search range."""
    source = textwrap.dedent("""\
      procedure main()
          int x
          x += 1
    """)
    program = parse_program("test.ja", source)
    validate_program(program)

    # x starts at whatever search gives, then x += 1.
    # We want x = 1000, but search range is 0..9
    # x_final = x_init + 1. For x_final=1000 we need x_init=999 -- not in range.
    result = find_input(
      program,
      output_var="x",
      target_value=1000,
      free_vars=["x"],
      search_range=range(0, 10),
    )
    self.assertIsNone(result)


class TestErrorCases(unittest.TestCase):
  """Test error handling in the inverse interpreter."""

  def test_no_main(self) -> None:
    """Program without main procedure."""
    source = textwrap.dedent("""\
      procedure helper(int x)
          x += 1
    """)
    result = run_inverse_from_source(source, {"x": 1})
    self.assertFalse(result.success)
    self.assertIn("main", result.error.lower())

  def test_impossible_assertion(self) -> None:
    """Program with assertion that fails during inversion."""
    source = textwrap.dedent("""\
      procedure main()
          int x
          x += 5
          assert x = 5
    """)
    # Inversion: assert x=5 first (with x=999, this fails)
    result = run_inverse_from_source(source, {"x": 999})
    self.assertFalse(result.success)
    self.assertIsNotNone(result.error)

  def test_invalid_source(self) -> None:
    """Malformed source code."""
    result = run_inverse_from_source("not valid jana code !!!", {"x": 1})
    self.assertFalse(result.success)
    self.assertIn("error", result.error.lower())


class TestWithProcedureCalls(unittest.TestCase):
  """Test inverse with programs that call procedures."""

  def test_call_procedure(self) -> None:
    """Inverse with a procedure call."""
    source = textwrap.dedent("""\
      procedure add_ten(int x)
          x += 10

      procedure main()
          int x
          call add_ten(x)
    """)
    result = run_inverse_from_source(source, {"x": 10})
    self.assertTrue(result.success, result.error)
    self.assertEqual(result.initial_store["x"], 0)

  def test_nested_calls(self) -> None:
    """Inverse with nested procedure calls."""
    source = textwrap.dedent("""\
      procedure inc(int x)
          x += 1

      procedure add_three(int x)
          call inc(x)
          call inc(x)
          call inc(x)

      procedure main()
          int x
          call add_three(x)
    """)
    result = run_inverse_from_source(source, {"x": 3})
    self.assertTrue(result.success, result.error)
    self.assertEqual(result.initial_store["x"], 0)


class TestFromLoop(unittest.TestCase):
  """Test inverse with from-loop constructs."""

  def test_counting_loop(self) -> None:
    """Inverse of a counting loop."""
    source = textwrap.dedent("""\
      procedure main()
          int x
          int n
          from n = 0 loop
              n += 1
              x += n
          until n = 5
    """)
    # Forward: n goes 0->5, x = 1+2+3+4+5 = 15
    result = run_inverse_from_source(source, {"x": 15, "n": 5})
    self.assertTrue(result.success, result.error)
    self.assertEqual(result.initial_store["x"], 0)
    self.assertEqual(result.initial_store["n"], 0)


if __name__ == "__main__":
  unittest.main()
