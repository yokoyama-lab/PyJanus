"""Expression (value) arguments to procedure calls: `call f(n-1, r)`.

A non-l-value argument passed to a non-constant parameter is bound to a fresh
local on entry and must read back the same value when the call returns — i.e.
`call f(n-1, r)` behaves like `local t = n-1; call f(t, r); delocal t = n-1`.
This keeps the call reversible.
"""
from __future__ import annotations

from pathlib import Path
import shutil
import subprocess
import sys
import textwrap
import unittest
import copy

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from jana_py.errors import JanaError
from jana_py.parser_jana2014 import parse_program
from jana_py.parser_janus2026 import parse_program as parse_program_2026
from jana_py.validate import validate_program
from jana_py.runtime import Runtime


def run_and_get_store(source: str, mod_bits: int | None = None) -> dict[str, object]:
  program = parse_program("valarg.ja", textwrap.dedent(source))
  validate_program(program)
  rt = Runtime(program, mod_bits=mod_bits)
  rt.run()
  assert rt._root_frame is not None
  return {k: copy.deepcopy(c.value) for k, c in rt._root_frame.vars.items()}


def run_2026_and_get_store(source: str) -> dict[str, object]:
  program = parse_program_2026("valarg.ja", textwrap.dedent(source))
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
    # value argument is bound to a scoped temp typed like the parameter
    # (not passed by reference)...
    self.assertIn("int _va0", cpp)
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
    self.assertEqual(cpp.count("int _va0"), 2)
    self.assertEqual(cpp.count("{"), cpp.count("}"))

  def test_value_arg_normalized_to_param_type(self) -> None:
    # The post-call restore check must normalize the re-evaluated expression to
    # the parameter's type, exactly like the bind: with x = 0, `x - 1` binds 255
    # to the `u8` parameter and must compare 255 (not -1) on return.
    store = run_2026_and_get_store("""\
      void addn(u8 n, int acc) { acc += n; }
      void main() { int x; int acc; call addn(x - 1, acc); }
      """)
    self.assertEqual(store["acc"], 255)
    self.assertEqual(store["x"], 0)

  def test_bool_expression_to_bool_param_works(self) -> None:
    # The restore check's bool branch: a bool value arg binds and reads back.
    store = run_and_get_store("""\
      procedure use(bool flag, int acc)
          if flag then
              acc += 1
          fi flag

      procedure main()
          int acc
          call use(1 < 2, acc)
      """)
    self.assertEqual(store["acc"], 1)

  def test_codegen_value_arg_temp_uses_param_type(self) -> None:
    # The C++ temp must be declared with the parameter's type — an `auto` temp
    # deduces the promoted `int` and cannot bind to a `signed char&` parameter.
    from jana_py.c_codegen import format_program as format_c_program
    program = parse_program_2026(
      "vl.ja",
      "void addn(i8 n, int acc) { acc += n; }\n"
      "void main() { int x; int acc; x += 9; call addn(x - 2, acc); }\n",
    )
    validate_program(program)
    cpp = format_c_program(None, program)
    self.assertIn("signed char _va0 = (x - 2);", cpp)
    self.assertNotIn("auto _va0", cpp)
    # the restore check normalizes the re-evaluated expression like the bind
    self.assertIn("if (_va0 != (signed char)((x - 2)))", cpp)

  def test_codegen_constant_param_value_arg_has_no_restore_check(self) -> None:
    # The interpreter snapshots an expression to a `constant` parameter without
    # a restore check; the generated C++ must not check (and so not throw on
    # valid programs whose constant argument reads differently after the call).
    from jana_py.c_codegen import format_program as format_c_program
    program = parse_program_2026(
      "vl.ja",
      "void f(constant int k, int y) { y += k; }\n"
      "void main() { int x; x += 3; call f(x + 1, x); }\n",
    )
    validate_program(program)
    cpp = format_c_program(None, program)
    self.assertIn("int _va0 = (x + 1);", cpp)  # still bound to a scoped temp
    self.assertNotIn('throw "Value argument is not restored on return"', cpp)

  @unittest.skipUnless(shutil.which("g++"), "g++ not available")
  def test_codegen_value_args_compile_with_gpp(self) -> None:
    # The generated C++ for sized-int and constant-param value arguments must
    # actually compile (regression: `auto` temps could not bind to `T&`).
    from jana_py.c_codegen import format_program as format_c_program
    program = parse_program_2026(
      "vl.ja",
      "void addn(i8 n, int acc) { acc += n; }\n"
      "void usek(constant u8 k, int acc) { acc += k; }\n"
      "void main() { int x; int acc; x += 9; call addn(x - 2, acc); call usek(x + 1, acc); }\n",
    )
    validate_program(program)
    cpp = format_c_program(None, program)
    proc = subprocess.run(
      ["g++", "-std=c++17", "-fsyntax-only", "-x", "c++", "-"],
      input=cpp, capture_output=True, text=True,
    )
    self.assertEqual(proc.returncode, 0, proc.stderr)

  def test_value_arg_to_array_param_is_rejected(self) -> None:
    # A non-l-value argument is only valid for scalar (int/bool) parameters.
    with self.assertRaises(JanaError) as ctx:
      run_2026_and_get_store("""\
        void f(int a[3], int acc) { acc += a[0]; }
        void main() { int x; int acc; call f(x + 1, acc); }
        """)
    self.assertIn("scalar", str(ctx.exception))

  def test_value_arg_to_stack_param_is_rejected(self) -> None:
    with self.assertRaises(JanaError) as ctx:
      run_and_get_store("""\
        procedure f(stack s, int acc)
            acc += 1
            acc -= 1

        procedure main()
            int x
            int acc
            call f(x + 1, acc)
        """)
    self.assertIn("scalar", str(ctx.exception))

  def test_two_value_args_in_one_call(self) -> None:
    store = run_and_get_store("""\
      procedure add2(int a, int b, int acc)
          acc += a
          acc += b

      procedure main()
          int x = 10
          int acc
          call add2(x - 1, x + 1, acc)
      """)
    self.assertEqual(store["acc"], 20)  # 9 + 11
    self.assertEqual(store["x"], 10)

  def test_value_arg_invalidated_through_reference_param_is_error(self) -> None:
    # The value argument `a + 1` reads `a`, which the callee net-modifies
    # through the by-reference parameter — the expression no longer reads back
    # its bound value on return, so the call is irreversible and must fail.
    with self.assertRaises(JanaError) as ctx:
      run_and_get_store("""\
        procedure f(int n, int a)
            a += n

        procedure main()
            int a = 3
            call f(a + 1, a)
        """)
    self.assertIn("not restored", str(ctx.exception))

  def test_uncall_value_argument_not_restored_is_error(self) -> None:
    # The restore check runs after uncall too: inverted `bump` net-modifies
    # its first parameter, so the value argument cannot read back.
    with self.assertRaises(JanaError) as ctx:
      run_and_get_store("""\
        procedure bump(int x, int acc)
            x += 1
            acc += x

        procedure main()
            int n = 5
            int acc
            uncall bump(n - 1, acc)
        """)
    self.assertIn("not restored", str(ctx.exception))

  def test_value_arg_normalized_under_mod_bits(self) -> None:
    # Under -m the bind normalizes the bound value; the restore check must
    # normalize the re-evaluated expression the same way (the untyped-int
    # branch of `_normalize_int`, as opposed to the sized `u8` test above).
    store = run_and_get_store("""\
      procedure addn(int n, int acc)
          acc += n

      procedure main()
          int x
          int acc
          x += 100
          call addn(x + 50, acc)
      """, mod_bits=8)
    self.assertEqual(store["acc"], -106)  # 150 mod 2^8, signed

  def test_invert_preserves_expression_args(self) -> None:
    # `-i` (global) inversion inverts procedure bodies and keeps calls; the
    # expression argument must survive inversion + formatting verbatim.
    from jana_py.invert import invert_program
    from jana_py.format import formatter_for_std
    program = parse_program("valarg.ja", textwrap.dedent("""\
      procedure addn(int n, int acc)
          acc += n

      procedure main()
          int x = 7
          int acc
          call addn(x - 2, acc)
      """))
    validate_program(program)
    inverted = invert_program(program)
    text = formatter_for_std("jana2014").format_program(inverted)
    self.assertIn("call addn(x - 2, acc)", text)
    self.assertIn("acc -= n", text)  # the body was inverted

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
