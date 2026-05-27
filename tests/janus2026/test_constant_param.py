from __future__ import annotations

from pathlib import Path
import sys
import textwrap
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src"))

from jana_py.errors import JanaError
from jana_py.invert import invert_program
from jana_py.parser_janus2026 import parse_program
from jana_py.runtime import Runtime


def run(source: str) -> Runtime:
  program = parse_program("test.ja", textwrap.dedent(source))
  rt = Runtime(program)
  rt.run()
  return rt


def run_inverse(source: str) -> Runtime:
  program = parse_program("test.ja", textwrap.dedent(source))
  program = invert_program(program)
  rt = Runtime(program)
  rt.run()
  return rt


class TestConstantParam(unittest.TestCase):
  def test_read_constant_param(self):
    """constant int k can be read in expressions."""
    rt = run("""\
      void main() {
          int k;
          int x;
          k += 5;
          call foo(k, x);
      }

      void foo(constant int k, int x) {
          x += k;
      }
    """)
    self.assertEqual(rt._root_frame.vars["x"].value, 5)

  def test_write_constant_param_rejected(self):
    """k += 1 is rejected when k is a constant param."""
    with self.assertRaises(JanaError) as ctx:
      run("""\
        void main() {
            int k;
            call foo(k);
        }

        void foo(constant int k) {
            k += 1;
        }
      """)
    self.assertIn("Updating constant", ctx.exception.message)

  def test_swap_constant_param_rejected(self):
    """k <=> x is rejected when k is constant."""
    with self.assertRaises(JanaError) as ctx:
      run("""\
        void main() {
            int k;
            int x;
            call foo(k, x);
        }

        void foo(constant int k, int x) {
            k <=> x;
        }
      """)
    self.assertIn("Updating constant", ctx.exception.message)

  def test_constant_array_param_read(self):
    """Elements of a constant array param can be read."""
    rt = run("""\
      void main() {
          int a[3];
          int x;
          a[0] += 10;
          a[1] += 20;
          a[2] += 30;
          call foo(a, x);
      }

      void foo(constant int a[3], int x) {
          x += a[1];
      }
    """)
    self.assertEqual(rt._root_frame.vars["x"].value, 20)

  def test_constant_array_param_write_rejected(self):
    """Writing to a constant array param element is rejected."""
    with self.assertRaises(JanaError) as ctx:
      run("""\
        void main() {
            int a[3];
            call foo(a);
        }

        void foo(constant int a[3]) {
            a[0] += 1;
        }
      """)
    self.assertIn("Updating constant", ctx.exception.message)

  def test_constant_stack_param_push_rejected(self):
    """push to a constant stack param is rejected."""
    with self.assertRaises(JanaError) as ctx:
      run("""\
        void main() {
            int s;
            call foo(s);
        }

        void foo(constant int s) {
            s += 1;
        }
      """)
    self.assertIn("Updating constant", ctx.exception.message)

  def test_mixed_params(self):
    """constant k is read-only, non-constant x is writable."""
    rt = run("""\
      void main() {
          int k;
          int x;
          k += 7;
          call foo(k, x);
      }

      void foo(constant int k, int x) {
          x += k;
      }
    """)
    self.assertEqual(rt._root_frame.vars["k"].value, 7)
    self.assertEqual(rt._root_frame.vars["x"].value, 7)

  def test_uncall_constant_param(self):
    """uncall also enforces constant param constraint."""
    with self.assertRaises(JanaError) as ctx:
      run("""\
        void main() {
            int k;
            uncall foo(k);
        }

        void foo(constant int k) {
            k += 1;
        }
      """)
    self.assertIn("Updating constant", ctx.exception.message)

  def test_inverse_execution(self):
    """Inverse execution with constant params works without error.

    invert_program inverts proc bodies but keeps main as-is.
    Forward: k=5, foo does x+=k → x=5.
    Inverse: foo body inverted to x-=k → x=-5.
    """
    rt = run_inverse("""\
      void main() {
          int k;
          int x;
          k += 5;
          call foo(k, x);
      }

      void foo(constant int k, int x) {
          x += k;
      }
    """)
    self.assertEqual(rt._root_frame.vars["k"].value, 5)
    self.assertEqual(rt._root_frame.vars["x"].value, -5)

  def test_caller_value_unchanged(self):
    """After call, the caller's variable bound to constant param is unchanged."""
    rt = run("""\
      void main() {
          int k;
          int x;
          k += 42;
          call foo(k, x);
      }

      void foo(constant int k, int x) {
          x += k;
      }
    """)
    self.assertEqual(rt._root_frame.vars["k"].value, 42)
    self.assertEqual(rt._root_frame.vars["x"].value, 42)


if __name__ == "__main__":
  unittest.main()
