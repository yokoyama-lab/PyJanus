"""Tests for the reversible `*=` / `/=` assignment operators (jana2014).

`x *= e` multiplies x by e and is inverted to `x /= e`; both directions are
only defined when no information is destroyed:
  - `*=` requires e != 0 (x == 0 is fine: x -> x*e is injective for e != 0)
  - `/=` requires e != 0 and exact divisibility (no remainder)
"""
from __future__ import annotations

from pathlib import Path
import sys
import textwrap
import unittest
import copy

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from jana_py.errors import JanaError
from jana_py.parser_jana2014 import parse_program
from jana_py.validate import validate_program
from jana_py.runtime import Runtime
from jana_py.invert import invert_program
from jana_py.ast import AssignStmt, ModOp


def run_and_get_store(source: str) -> dict[str, object]:
  program = parse_program("mul_test.ja", textwrap.dedent(source))
  validate_program(program)
  rt = Runtime(program)
  rt.run()
  assert rt._root_frame is not None
  return {k: copy.deepcopy(c.value) for k, c in rt._root_frame.vars.items()}


class MulDivParseTests(unittest.TestCase):

  def _parse_main_ops(self, body: str) -> list[ModOp]:
    program = parse_program("mul_test.ja", textwrap.dedent(f"""\
      procedure main()
          int x = 6
      {body}
      """))
    return [stmt.mod_op for stmt in program.main.stmts if isinstance(stmt, AssignStmt)]

  def test_parse_mul_eq(self) -> None:
    self.assertEqual(self._parse_main_ops("    x *= 3"), [ModOp.MUL_EQ])

  def test_parse_div_eq(self) -> None:
    self.assertEqual(self._parse_main_ops("    x /= 3"), [ModOp.DIV_EQ])

  def test_mul_does_not_shadow_exponent(self) -> None:
    # `**` (exponent) must still tokenize; `x *= 2 ** 3` is x *= 8.
    store = run_and_get_store("""\
      procedure main()
          int x = 5
          x *= 2 ** 3
          x -= 40
      """)
    self.assertEqual(store["x"], 0)


class MulDivRuntimeTests(unittest.TestCase):

  def test_mul_eq_forward(self) -> None:
    store = run_and_get_store("""\
      procedure main()
          int x = 7
          x *= 3
          x -= 21
      """)
    self.assertEqual(store["x"], 0)

  def test_div_eq_forward(self) -> None:
    store = run_and_get_store("""\
      procedure main()
          int x = 21
          x /= 3
          x -= 7
      """)
    self.assertEqual(store["x"], 0)

  def test_mul_then_div_is_identity(self) -> None:
    store = run_and_get_store("""\
      procedure main()
          int x = 7
          x *= 3
          x /= 3
          x -= 7
      """)
    self.assertEqual(store["x"], 0)

  def test_array_element_mul_div(self) -> None:
    store = run_and_get_store("""\
      procedure main()
          int a[2]
          a[0] += 5
          a[0] *= 4
          a[0] /= 4
          a[0] -= 5
      """)
    self.assertEqual(store["a"], [0, 0])

  def test_mul_by_zero_fails(self) -> None:
    with self.assertRaises(JanaError) as ctx:
      run_and_get_store("""\
        procedure main()
            int x = 7
            x *= 0
            x += 1
        """)
    self.assertIn("Multiplication by zero", str(ctx.exception))

  def test_mul_zero_multiplicand_ok(self) -> None:
    # x == 0 is allowed: x -> x*c is injective for c != 0
    # (0 *= 3 -> 0, recovered by 0 /= 3 -> 0).
    store = run_and_get_store("""\
        procedure main()
            int x
            x *= 3
            x += 1
        """)
    self.assertEqual(store["x"], 1)

  def test_div_by_zero_fails(self) -> None:
    with self.assertRaises(JanaError) as ctx:
      run_and_get_store("""\
        procedure main()
            int x = 7
            x /= 0
            x += 1
        """)
    self.assertIn("Division by zero", str(ctx.exception))

  def test_div_with_remainder_fails(self) -> None:
    with self.assertRaises(JanaError) as ctx:
      run_and_get_store("""\
        procedure main()
            int x = 7
            x /= 2
            x += 1
        """)
    self.assertIn("Division remains", str(ctx.exception))


class MulDivReversibilityTests(unittest.TestCase):

  def test_call_uncall_restores_state(self) -> None:
    store = run_and_get_store("""\
      procedure scale(int x)
          x *= 3
          x /= 3

      procedure main()
          int a = 7
          call scale(a)
          uncall scale(a)
          a -= 7
      """)
    self.assertEqual(store["a"], 0)

  def test_invert_swaps_mul_and_div(self) -> None:
    program = parse_program("mul_test.ja", textwrap.dedent("""\
      procedure scale(int x)
          x *= 3
          x /= 5

      procedure main()
          int a = 15
          call scale(a)
      """))
    inverted = invert_program(program)
    proc = inverted.procs[0]
    # Inversion reverses statement order and maps *= <-> /=.
    self.assertEqual([s.mod_op for s in proc.body], [ModOp.MUL_EQ, ModOp.DIV_EQ])


def run_and_get_store_mod(source: str, mod_bits: int | None = None, mod_prime: int | None = None) -> dict[str, object]:
  program = parse_program("mul_test.ja", textwrap.dedent(source))
  validate_program(program)
  rt = Runtime(program, mod_bits=mod_bits, mod_prime=mod_prime)
  rt.run()
  assert rt._root_frame is not None
  return {k: copy.deepcopy(c.value) for k, c in rt._root_frame.vars.items()}


class MulDivModularTests(unittest.TestCase):
  """Under -m/-p, *= must stay injective and /= must be its exact inverse."""

  def test_mod_bits_odd_factor_round_trips_through_wraparound(self) -> None:
    # 200 *= 3 = 600 wraps mod 256; /= 3 must recover 200 via the modular inverse.
    store = run_and_get_store_mod("""\
      procedure main()
          int x = 200
          x *= 3
          x /= 3
          x -= 200
      """, mod_bits=8)
    self.assertEqual(store["x"], 0)

  def test_mod_bits_even_factor_is_rejected(self) -> None:
    # mod 256, x -> 2*x collapses x and x+128: not injective.
    with self.assertRaises(JanaError) as ctx:
      run_and_get_store_mod("""\
        procedure main()
            int x = 128
            x *= 2
        """, mod_bits=8)
    self.assertIn("not invertible", str(ctx.exception))

  def test_mod_prime_any_nonzero_factor_round_trips(self) -> None:
    # In a prime field every nonzero factor is invertible, including even ones.
    store = run_and_get_store_mod("""\
      procedure main()
          int x = 5
          x *= 2
          x /= 2
          x -= 5
      """, mod_prime=7)
    self.assertEqual(store["x"], 0)

  def test_mod_prime_factor_divisible_by_p_is_rejected(self) -> None:
    with self.assertRaises(JanaError) as ctx:
      run_and_get_store_mod("""\
        procedure main()
            int x = 5
            x *= 7
        """, mod_prime=7)
    self.assertIn("not invertible", str(ctx.exception))


class MulDivCodegenTests(unittest.TestCase):
  """Generated C++ must carry the same reversibility guards as the interpreter."""

  def test_cpp_guards_for_mul_and_div(self) -> None:
    from jana_py.c_codegen import format_program as format_c_program
    program = parse_program("mul_test.ja", textwrap.dedent("""\
      procedure main()
          int x = 21
          x *= 2
          x /= 6
      """))
    cpp = format_c_program(None, program)
    self.assertIn('throw "Multiplication by zero"', cpp)
    self.assertIn('throw "Division by zero"', cpp)
    self.assertIn('throw "Division remains"', cpp)


if __name__ == "__main__":
  unittest.main()
