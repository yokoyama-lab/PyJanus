"""Differential test: *run* the generated C++ and compare it to the interpreter.

The existing C++ codegen tests only `-fsyntax-only` the output, so a backend that
emits compilable-but-wrong code slips through.  Running the generator against the
interpreter found five such bugs, each regression-tested here:
  * uninitialized locals (`int x;` -> garbage instead of 0);
  * the `from..do..loop..until` off-by-one (dropped the trailing do-part);
  * `uncall` was emitted as a comment (a no-op);
  * a procedure's inverse called the *forward* callee instead of its inverse;
  * `iterate ... by -1` used a fixed `<=` bound, so descending/ inverse loops
    never ran.
These compile at -O0 (which exposes uninitialized reads) and check the run.
"""
from __future__ import annotations

import copy
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


def _build(source: str):
  program = parse_program("cg.ja", textwrap.dedent(source))
  validate_program(program)
  return program


def _interp(program) -> dict:
  rt = Runtime(program)
  rt.run()
  return {k: copy.deepcopy(c.value) for k, c in rt._root_frame.vars.items()}


@unittest.skipUnless(shutil.which("g++"), "g++ not available")
class CodegenRunTests(unittest.TestCase):

  def _run_cpp(self, program) -> dict[str, int]:
    scal = [vd.ident.name for vd in program.main.vdecls if not vd.dimensions]
    arrs = {vd.ident.name: int(vd.dimensions[0].value)
            for vd in program.main.vdecls if len(vd.dimensions) == 1}
    prints = "".join(f'std::cout << "@{n}=" << {n} << "\\n";' for n in scal)
    prints += "".join(f'std::cout << "@{n}[{i}]=" << {n}[{i}] << "\\n";'
                      for n, d in arrs.items() for i in range(d))
    cpp = format_program(None, program).replace("return 1;", prints + "return 0;")
    comp = subprocess.run(["g++", "-std=c++17", "-O0", "-x", "c++", "-", "-o", "/tmp/_cgt"],
                          input=cpp, capture_output=True, text=True)
    self.assertEqual(comp.returncode, 0, comp.stderr)
    run = subprocess.run(["/tmp/_cgt"], capture_output=True, text=True, timeout=10)
    got = {}
    for line in run.stdout.splitlines():
      if line.startswith("@"):
        k, v = line[1:].split("=", 1)
        got[k] = int(v)
    return got

  def _assert_matches(self, source: str) -> dict:
    program = _build(source)
    expected = _interp(program)
    got = self._run_cpp(program)
    for vd in program.main.vdecls:
      n = vd.ident.name
      if vd.dimensions:
        cells = expected.get(n, [])
        for i in range(int(vd.dimensions[0].value)):
          ev = int(cells[i]) if i < len(cells) else 0
          self.assertEqual(got[f"{n}[{i}]"], ev, f"{n}[{i}]")
      else:
        self.assertEqual(got[n], int(expected[n]), n)
    return got

  def test_uninitialized_locals_are_zero(self) -> None:
    got = self._assert_matches("""\
        procedure main()
            int x
            int a[3]
            x += 5
            a[1] += 7
        """)
    self.assertEqual(got["x"], 5)
    self.assertEqual(got["a[0]"], 0)

  def test_from_loop_offbyone(self) -> None:
    # do-part runs once more than the loop-part: x += 2 four times -> 18.
    got = self._assert_matches("""\
        procedure main()
            int x
            int i
            x += 10
            from i = 0 do
                x += 2
            loop
                i += 1
            until i = 3
        """)
    self.assertEqual(got["x"], 18)

  def test_uncall_inverts_a_call(self) -> None:
    got = self._assert_matches("""\
        procedure inc(int a)
            a += 1
        procedure main()
            int x
            int y
            x += 5
            call inc(x)
            call inc(y)
            uncall inc(y)
        """)
    self.assertEqual(got["x"], 6)
    self.assertEqual(got["y"], 0)

  def test_recursive_uncall_roundtrips(self) -> None:
    # call fib then uncall fib must restore the initial store exactly.
    self._assert_matches("""\
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
            uncall fib(x1, x2, n)
        """)

  def test_proc_var_name_collision(self) -> None:
    # Janus keeps procedures and variables in separate namespaces; C++ does not,
    # so a procedure named like an in-scope variable must be renamed.
    program = _build("""\
        procedure root(int num, int r)
            r += num
        procedure main()
            int num
            int root
            num += 7
            call root(num, root)
        """)
    cpp = format_program(None, program)
    self.assertNotIn("void root(", cpp)        # renamed to avoid the clash
    got = self._run_cpp(program)
    self.assertEqual(got["root"], 7)

  def test_descending_iterate(self) -> None:
    got = self._assert_matches("""\
        procedure main()
            int s
            iterate int i = 5 by -1 to 1
                s += i
            end
        """)
    self.assertEqual(got["s"], 15)


if __name__ == "__main__":
  unittest.main()
