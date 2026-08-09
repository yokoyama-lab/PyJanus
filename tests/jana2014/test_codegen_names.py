"""Targeted regression tests for the C++ back-end's name and type handling.

The corpus test (`test_codegen_corpus.py`) compiles every example and would also
catch these, but only as "some program failed to compile"; these pin the three
specific defects that hid behind skipped corpus entries:

  * a Janus identifier that is a C++ keyword (`procedure delete`) was emitted
    verbatim, so `delete(k)` parsed as the delete operator;
  * a struct variable was emitted as `Point p = 0;`, which is not valid C++;
  * a rank-2 array parameter was emitted as `int*`, but `int A[3][3]` decays to
    `int (*)[3]`.
"""
from __future__ import annotations

import subprocess
import shutil
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from jana_py.parser_jana2014 import parse_program        # noqa: E402
from jana_py.validate import validate_program            # noqa: E402
from jana_py.c_codegen import format_program             # noqa: E402
from jana_py.errors import JanaError                     # noqa: E402


def gen(src: str) -> str:
  program = parse_program("<test>", src)
  validate_program(program)
  return format_program(None, program)


def compiles(cpp: str) -> tuple[bool, str]:
  if not shutil.which("g++"):
    raise unittest.SkipTest("g++ not available")
  proc = subprocess.run(["g++", "-std=c++17", "-fsyntax-only", "-x", "c++", "-"],
                        input=cpp, capture_output=True, text=True)
  return proc.returncode == 0, proc.stderr


class CodegenNameTests(unittest.TestCase):

  def test_cpp_keyword_procedure_is_renamed(self) -> None:
    cpp = gen("procedure delete(int x)\n"
              "    x += 1\n"
              "\n"
              "procedure main()\n"
              "    int a\n"
              "    call delete(a)\n")
    self.assertNotIn("void delete(", cpp)
    self.assertIn("delete_", cpp)
    ok, err = compiles(cpp)
    self.assertTrue(ok, err)

  def test_cpp_keyword_variable_is_renamed(self) -> None:
    cpp = gen("procedure main()\n"
              "    int new\n"
              "    new += 2\n")
    self.assertNotIn("int new ", cpp)
    ok, err = compiles(cpp)
    self.assertTrue(ok, err)

  def test_struct_variable_is_zero_initialized(self) -> None:
    cpp = gen("struct Point {\n"
              "    int x;\n"
              "    int y;\n"
              "}\n"
              "\n"
              "procedure main()\n"
              "    Point p\n"
              "    p.x += 3\n")
    self.assertIn("Point p = {}", cpp)
    self.assertNotIn("Point p = 0", cpp)
    ok, err = compiles(cpp)
    self.assertTrue(ok, err)

  def test_local_struct_is_zero_initialized(self) -> None:
    cpp = gen("struct Point {\n"
              "    int x;\n"
              "    int y;\n"
              "}\n"
              "\n"
              "procedure main()\n"
              "    int s\n"
              "    local Point q\n"
              "        q.x += 1\n"
              "        s += q.x\n"
              "        q.x -= 1\n"
              "    delocal Point q\n")
    ok, err = compiles(cpp)
    self.assertTrue(ok, err)

  def test_rank2_array_parameter_keeps_its_extents(self) -> None:
    cpp = gen("procedure bump(int m[][], int n)\n"
              "    m[0][0] += n\n"
              "\n"
              "procedure main()\n"
              "    int g[3][3]\n"
              "    int k\n"
              "    k += 1\n"
              "    call bump(g, k)\n")
    self.assertIn("(*m)[3]", cpp)
    ok, err = compiles(cpp)
    self.assertTrue(ok, err)

  def test_primed_identifier_is_escaped(self) -> None:
    # The lexer admits `'` in identifiers, so `inc'` is a legal Janus name; the
    # generator used to copy it verbatim and emit `void inc'(int& x');`, where
    # the `'` opens a C++ character literal.
    cpp = gen("procedure inc'(int x')\n"
              "    x' += 1\n"
              "\n"
              "procedure main()\n"
              "    int a = 0\n"
              "    call inc'(a)\n")
    self.assertNotIn("'", cpp)
    self.assertIn("inc_prime", cpp)
    ok, err = compiles(cpp)
    self.assertTrue(ok, err)

  def test_escaping_two_names_apart_stays_injective(self) -> None:
    # `x'` and `x_prime` are different Janus names and must stay different C++
    # ones; a naive `'` -> `_prime` substitution collapses them.
    cpp = gen("procedure main()\n"
              "    int x'\n"
              "    int x_prime\n"
              "    x' += 1\n"
              "    x_prime += 2\n")
    ok, err = compiles(cpp)
    self.assertTrue(ok, err)

  def test_procedure_named_like_a_global_library_function(self) -> None:
    # `<cstdlib>` declares `::div` at global scope, so an emitted global
    # `void div(int&, int&)` made the call site ambiguous.  Which library names
    # are visible at global scope is toolchain-dependent, so the defence is the
    # namespace, not a list.
    cpp = gen("procedure div(int x, int y)\n"
              "    x += y\n"
              "\n"
              "procedure main()\n"
              "    int a = 1\n"
              "    int b = 2\n"
              "    call div(a, b)\n")
    self.assertIn("namespace jana_user {", cpp)
    ok, err = compiles(cpp)
    self.assertTrue(ok, err)

  def test_every_user_name_is_emitted_inside_the_namespace(self) -> None:
    cpp = gen("procedure main()\n"
              "    int a\n"
              "    a += 1\n")
    body = cpp.split("namespace jana_user {", 1)[1]
    tail = body.rsplit("}  // namespace jana_user", 1)[1]
    # Nothing but the trampoline may live at global scope.
    self.assertEqual(tail.strip(), "int main() { return jana_user::main(); }")


class ValidatorTests(unittest.TestCase):

  def test_call_to_undefined_procedure_is_rejected(self) -> None:
    with self.assertRaises(Exception) as cm:
      gen("procedure helper(int x)\n"
          "    call missing(x)\n"
          "\n"
          "procedure main()\n"
          "    int a\n"
          "    a += 1\n")
    self.assertIn("missing", str(cm.exception))

  # `push` moves its operand onto the stack and zeroes it, so the operand has to
  # be a place.  The interpreter enforced this for `pop` only, which left the
  # language not closed under inversion (`push(1, s)` ran, its inverse could
  # not), and the back-end emitted `s.push_back(1); 1 = 0;`.  Pin all three
  # layers: validator rejects, generator declines, and the literal form has a
  # mechanical l-value rewrite that still works.

  PUSH_LITERAL = ("procedure main()\n"
                  "    stack s = nil\n"
                  "    int m = 0\n"
                  "    push(1, s)\n"
                  "    pop(m, s)\n"
                  "    m -= 1\n")

  def test_push_of_a_non_lvalue_is_rejected(self) -> None:
    with self.assertRaises(JanaError) as cm:
      gen(self.PUSH_LITERAL)
    self.assertIn("l-values are supported for push", str(cm.exception))

  def test_pop_of_a_non_lvalue_is_rejected(self) -> None:
    with self.assertRaises(JanaError) as cm:
      gen("procedure main()\n"
          "    stack s = nil\n"
          "    int m = 1\n"
          "    push(m, s)\n"
          "    pop(0, s)\n")
    self.assertIn("l-values are supported for pop", str(cm.exception))

  def test_generator_declines_a_non_lvalue_push_without_the_validator(self) -> None:
    # Defence in depth: a caller that skips validation must get a raise, not
    # C++ containing `1 = 0;`.
    program = parse_program("<test>", self.PUSH_LITERAL)
    with self.assertRaises(ValueError) as cm:
      format_program(None, program)
    self.assertIn("l-values are supported for push", str(cm.exception))

  def test_the_lvalue_rewrite_of_a_literal_push_is_accepted(self) -> None:
    cpp = gen("procedure main()\n"
              "    stack s = nil\n"
              "    int m = 0\n"
              "    local int t = 1\n"
              "        push(t, s)\n"
              "    delocal int t = 0\n"
              "    pop(m, s)\n"
              "    m -= 1\n")
    ok, err = compiles(cpp)
    self.assertTrue(ok, err)


if __name__ == "__main__":
  unittest.main()
