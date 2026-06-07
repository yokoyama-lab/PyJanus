"""Tests for the reversible `*=` / `/=` assignment operators (jana2014).

`x *= e` multiplies x by e and is inverted to `x /= e`; both directions are
only defined when neither side destroys information:
  - `*=` requires e != 0 and x != 0 (zero would erase the old value)
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

  def test_mul_zero_multiplicand_fails(self) -> None:
    with self.assertRaises(JanaError) as ctx:
      run_and_get_store("""\
        procedure main()
            int x
            x *= 3
            x += 1
        """)
    self.assertIn("Multiplicand is zero", str(ctx.exception))

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


if __name__ == "__main__":
  unittest.main()
