"""Differential test: *run* the generated C++ and compare it to the interpreter.

The existing C++ codegen tests only `-fsyntax-only` the output, so a backend that
emits compilable-but-wrong code slips through.  Regression target: Janus
default-initializes every variable to 0, but the codegen used to emit bare
`int x;` (indeterminate in C++), so an optimized build could read garbage.  These
tests compile at -O0 (which exposes uninitialized reads) and check the run.
"""
from __future__ import annotations

import copy
import re
import shutil
import subprocess
import sys
import textwrap
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from jana_py.parser_jana2014 import parse_program
from jana_py.validate import validate_program
from jana_py.runtime import Runtime
from jana_py.c_codegen import format_program


def _compile(source: str):
  program = parse_program("cg.ja", textwrap.dedent(source))
  validate_program(program)
  return program


def _interp_scalars(program) -> dict[str, int]:
  rt = Runtime(program)
  rt.run()
  assert rt._root_frame is not None
  return {k: copy.deepcopy(c.value) for k, c in rt._root_frame.vars.items()}


class CodegenRunTests(unittest.TestCase):

  def test_no_uninitialized_declarations(self) -> None:
    # Every declared variable must be explicitly zero-initialized.
    program = _compile("""\
        procedure main()
            int x
            int a[3]
            x += 5
            a[1] += 7
        """)
    cpp = format_program(None, program)
    self.assertIn("int x = 0;", cpp)
    self.assertIn("int a[3] = {};", cpp)
    self.assertNotRegex(cpp, r"\bint x;")     # the old, buggy form

  @unittest.skipUnless(shutil.which("g++"), "g++ not available")
  def test_generated_cpp_run_matches_interpreter(self) -> None:
    source = """\
        procedure main()
            int x
            int y
            int a[3]
            x += 5
            y += 3
            x += y
            a[0] += x
            a[2] += a[0]
        """
    program = _compile(source)
    expected = _interp_scalars(program)

    scalars = [vd.ident.name for vd in program.main.vdecls if not vd.dimensions]
    arrays = {vd.ident.name: int(vd.dimensions[0].value)
              for vd in program.main.vdecls if vd.dimensions}
    prints = "".join(f'std::cout << "{n}=" << {n} << "\\n";' for n in scalars)
    prints += "".join(
        f'std::cout << "{n}[{i}]=" << {n}[{i}] << "\\n";'
        for n, d in arrays.items() for i in range(d))

    cpp = format_program(None, program).replace("return 1;", prints + "return 0;")
    out = subprocess.run(["g++", "-std=c++17", "-O0", "-x", "c++", "-", "-o", "/tmp/_cgrun"],
                         input=cpp, capture_output=True, text=True)
    self.assertEqual(out.returncode, 0, out.stderr)
    run = subprocess.run(["/tmp/_cgrun"], capture_output=True, text=True)
    got = dict(m.split("=") for m in run.stdout.split())

    for n in scalars:
      self.assertEqual(int(got[n]), int(expected[n]), f"{n}: cpp={got[n]} interp={expected[n]}")
    for n, d in arrays.items():
      cells = expected[n]
      for i in range(d):
        self.assertEqual(int(got[f"{n}[{i}]"]), int(cells[i]),
                         f"{n}[{i}]: cpp={got[f'{n}[{i}]']} interp={cells[i]}")
    self.assertEqual(int(got["a[0]"]), 8)
    self.assertEqual(int(got["a[2]"]), 8)


if __name__ == "__main__":
  unittest.main()
