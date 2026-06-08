"""Expression (value) arguments to procedure calls: `call f(n-1, r)`.

A non-l-value argument passed to a non-constant parameter is bound to a fresh
local on entry and must read back the same value when the call returns — i.e.
`call f(n-1, r)` behaves like `local t = n-1; call f(t, r); delocal t = n-1`.
This keeps the call reversible.
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


def run_and_get_store(source: str) -> dict[str, object]:
  program = parse_program("valarg.ja", textwrap.dedent(source))
  validate_program(program)
  rt = Runtime(program)
  rt.run()
  assert rt._root_frame is not None
  return {k: copy.deepcopy(c.value) for k, c in rt._root_frame.vars.items()}


class ValueArgTests(unittest.TestCase):

  def test_expression_argument_passes_value(self) -> None:
    store = run_and_get_store("""\
      procedure addn(int n, int acc)
          acc += n

      procedure main()
          int x = 10
          int acc
          call addn(x - 3, acc)
      """)
    self.assertEqual(store["acc"], 7)
    self.assertEqual(store["x"], 10)  # unchanged

  def test_recursion_with_expression_argument(self) -> None:
    store = run_and_get_store("""\
      procedure sum_to(int n, int acc)
          if n = 0 then
              skip
          else
              acc += n
              call sum_to(n - 1, acc)
          fi n = 0

      procedure main()
          int n = 4
          int acc
          call sum_to(n, acc)
      """)
    self.assertEqual(store["acc"], 10)  # 4+3+2+1

  def test_call_then_uncall_is_identity(self) -> None:
    store = run_and_get_store("""\
      procedure addn(int n, int acc)
          acc += n

      procedure main()
          int x = 7
          int acc
          call addn(x - 2, acc)
          uncall addn(x - 2, acc)
      """)
    self.assertEqual(store["acc"], 0)
    self.assertEqual(store["x"], 7)

  def test_value_argument_not_restored_is_error(self) -> None:
    # `bump` net-modifies its first parameter, so the value argument cannot be
    # restored on return — this must be rejected, not silently miscomputed.
    with self.assertRaises(JanaError) as ctx:
      run_and_get_store("""\
        procedure bump(int x, int acc)
            x += 1
            acc += x

        procedure main()
            int n = 5
            int acc
            call bump(n - 1, acc)
        """)
    self.assertIn("not restored", str(ctx.exception))

  def test_constant_param_still_accepts_expression(self) -> None:
    store = run_and_get_store("""\
      procedure usek(constant int k, int acc)
          acc += k

      procedure main()
          int acc
          call usek(2 + 3, acc)
      """)
    self.assertEqual(store["acc"], 5)

  def test_codegen_emits_temp_and_check_for_value_arg(self) -> None:
    from jana_py.c_codegen import format_program as format_c_program
    program = parse_program("valarg.ja", textwrap.dedent("""\
      procedure addn(int n, int acc)
          acc += n

      procedure main()
          int x = 7
          int acc
          call addn(x - 2, acc)
      """))
    validate_program(program)
    cpp = format_c_program(None, program)
    # value argument is bound to a scoped temp (not passed by reference)...
    self.assertIn("auto _va0", cpp)
    # ...and checked for restoration on return
    self.assertIn('throw "Value argument is not restored on return"', cpp)

  def test_int_expression_to_bool_param_is_rejected(self) -> None:
    # A value argument is type-checked like an l-value argument: an int
    # expression must not silently bind to a bool parameter.
    with self.assertRaises(JanaError) as ctx:
      run_and_get_store("""\
        procedure use(bool flag, int acc)
            if flag then
                acc += 1
            fi flag

        procedure main()
            int x = 5
            int acc
            call use(x + 2, acc)
        """)
    self.assertIn("bool", str(ctx.exception))

  def test_bool_expression_to_int_param_is_rejected(self) -> None:
    with self.assertRaises(JanaError) as ctx:
      run_and_get_store("""\
        procedure addn(int n, int acc)
            acc += n

        procedure main()
            int acc
            call addn(2 < 3, acc)
        """)
    self.assertIn("int", str(ctx.exception))

  def test_codegen_two_value_arg_calls_on_one_line_dont_collide(self) -> None:
    # Each value-arg call wraps its temps in their own `{ }` scope, so two
    # calls sharing a source line do not redeclare the same C++ temp.
    from jana_py.c_codegen import format_program as format_c_program
    from jana_py.parser_janus2026 import parse_program as parse_2026
    program = parse_2026(
      "vl.ja",
      "void addn(int n, int acc) { acc += n; }\n"
      "void main() { int x; int acc; x += 9; call addn(x - 1, acc); call addn(x - 2, acc); }\n",
    )
    validate_program(program)
    cpp = format_c_program(None, program)
    # exactly two scoped temps, both named _va0 but in separate blocks
    self.assertEqual(cpp.count("auto _va0"), 2)
    self.assertEqual(cpp.count("{"), cpp.count("}"))

  def test_lvalue_argument_still_mutable(self) -> None:
    # A plain l-value argument is still pass-by-reference (not a value arg).
    store = run_and_get_store("""\
      procedure inc(int x)
          x += 1

      procedure main()
          int a = 4
          call inc(a)
      """)
    self.assertEqual(store["a"], 5)


if __name__ == "__main__":
  unittest.main()
