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

  # --- edge cases of the generated inverse (`uncall`) machinery ---

  def test_uncall_with_value_argument(self) -> None:
    # uncall passing an expression: the inverse is called with the value-arg temp.
    got = self._assert_matches("""\
        procedure add(int a, int b)
            a += b
        procedure main()
            int x
            int y
            x += 10
            y += 3
            call add(x, y + 1)
            uncall add(x, y + 1)
        """)
    self.assertEqual(got["x"], 10)
    self.assertEqual(got["y"], 3)

  def test_nested_call_then_uncall(self) -> None:
    self._assert_matches("""\
        procedure inc(int a)
            a += 1
        procedure twice(int a)
            call inc(a)
            call inc(a)
        procedure main()
            int x
            x += 5
            call twice(x)
            uncall twice(x)
        """)

  def test_internal_call_and_uncall_invert(self) -> None:
    # net's body mixes call and uncall; its inverse must swap both consistently.
    self._assert_matches("""\
        procedure inc(int a)
            a += 1
        procedure net(int a)
            call inc(a)
            call inc(a)
            uncall inc(a)
        procedure main()
            int x
            x += 5
            call net(x)
            uncall net(x)
        """)

  def test_stack_push_pop_top_empty(self) -> None:
    # Stacks compile to std::vector: push moves the value and zeroes the source,
    # pop restores it, top/empty/size read the vector. Checked against the
    # interpreter (incl. the stack's contents) by the differential driver.
    import sys
    import tempfile
    sys.path.insert(0, str(ROOT / "coq" / "harness"))
    import codegen_diff
    src = textwrap.dedent("""\
        procedure main()
            stack s
            int x
            int t
            x += 5
            push(x, s)
            x += 7
            push(x, s)
            t += top(s)
            pop(x, s)
        """)
    with tempfile.NamedTemporaryFile("w", suffix=".ja", delete=False) as f:
      f.write(src)
      path = f.name
    tag, msg = codegen_diff.check(path)
    self.assertEqual(tag, "PASS", msg)

  def test_size_of_array_parameter(self) -> None:
    # C++ array params are raw pointers; size(a) must resolve to the declared
    # length of the bound actual (b has 5 cells).
    got = self._assert_matches("""\
        procedure addsize(int a[], int acc)
            acc += size(a)
        procedure main()
            int b[5]
            int total
            call addsize(b, total)
        """)
    self.assertEqual(got["total"], 5)

  def test_local_delocal_in_uncalled_proc(self) -> None:
    got = self._assert_matches("""\
        procedure dbl(int a)
            local int t = 0
                t += a
                a += t
            delocal int t = a / 2
        procedure main()
            int x
            x += 4
            call dbl(x)
            uncall dbl(x)
        """)
    self.assertEqual(got["x"], 4)


if __name__ == "__main__":
  unittest.main()
