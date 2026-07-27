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


if __name__ == "__main__":
  unittest.main()
