"""Passing an array cell by reference: `call f(a[0])`.

Janus passes the CELL, not its value — `bump(a[1])` leaves 9 in `a[1]`, checked
against the interpreter below rather than assumed. So the encoding binds the
formal to that element's own variable, which is the same "one entity, two
names" the plain-variable case already relies on.

Two things have to hold, and the second is where this family of changes has
gone wrong before (the swap case once modelled `x <=> x` as the identity and
nuXmv *proved* a program the interpreter rejects):

1. the callee's writes reach the caller's array, and
2. the aliasing decision still matches the interpreter's, cell by cell.

A variable index stays refused: it names no single element, so there is nothing
to bind, and guessing is how the first mistake was made.
"""
import pathlib
import subprocess
import sys
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from jana_py import parser_jana2014, preprocess          # noqa: E402
from jana_py.smv import SmvUnsupported, compile_to_smv   # noqa: E402


def model_of(src: str, **kw) -> str:
  pt = preprocess.preprocess_text("<test>", src, None, "jana2014")
  program = parser_jana2014.parse_program("<test>", pt.text, pt.line_origins)
  return compile_to_smv(program, **kw)


def has_err_edge(model: str) -> bool:
  """A real transition into ERR, not the comment that names the location.

  Copied deliberately from `test_smv_alias.py`: a first attempt here matched
  `pc = 0` anywhere and so reported an ERR edge in a model whose only mention
  of it is the header comment — which would have been recorded as a false
  alarm in the encoding rather than in the test.
  """
  in_pc = False
  for line in model.splitlines():
    if line.strip().startswith("next(pc) :="):
      in_pc = True
      continue
    if in_pc:
      if line.strip() == "esac;":
        return False
      if line.strip().endswith(": 0;"):
        return True
  return False


def interpreter(src: str) -> tuple[int, str]:
  proc = subprocess.run([sys.executable, "-m", "jana_py.cli", "--std", "jana2014", "-s", "-"],
                        input=src, capture_output=True, text=True, cwd=ROOT, timeout=120)
  return proc.returncode, proc.stdout + proc.stderr


BY_REFERENCE = """
procedure bump(int x)
    x += 7

procedure main()
    int a[3]
    a[0] += 1
    a[1] += 2
    call bump(a[1])
"""

ALIASED_CELLS = """
procedure sw(int x, int y)
    x <=> y

procedure main()
    int a[3]
    a[0] += 1
    call sw(a[0], a[0])
"""

DISTINCT_CELLS = """
procedure sw(int x, int y)
    x <=> y

procedure main()
    int a[3]
    a[0] += 1
    a[1] += 2
    call sw(a[0], a[1])
"""

VARIABLE_INDEX = """
procedure bump(int x)
    x += 1

procedure main()
    int a[3]
    int i
    i += 1
    call bump(a[i])
"""


class TheInterpreterIsTheReference(unittest.TestCase):
  """Whatever the model says has to be measured against this, not against what
  the encoding's author believed the language does."""

  def test_a_cell_argument_is_passed_by_reference(self):
    rc, out = interpreter(BY_REFERENCE)
    self.assertEqual(rc, 0, out)
    self.assertIn("9", out, "the callee's write must reach the caller's array")

  def test_two_formals_on_one_cell_is_an_aliasing_error(self):
    rc, out = interpreter(ALIASED_CELLS)
    self.assertNotEqual(rc, 0)
    self.assertIn("aliases", out)

  def test_two_formals_on_different_cells_runs(self):
    rc, out = interpreter(DISTINCT_CELLS)
    self.assertEqual(rc, 0, out)


class TheEncodingAgrees(unittest.TestCase):
  def test_a_cell_argument_compiles(self):
    self.assertIn("pc", model_of(BY_REFERENCE, init="zero"))

  def test_aliased_cells_can_reach_err(self):
    self.assertTrue(has_err_edge(model_of(ALIASED_CELLS, init="zero")),
                    "the interpreter refuses this; the model must be able to fail")

  def test_distinct_cells_do_not_reach_err(self):
    self.assertFalse(has_err_edge(model_of(DISTINCT_CELLS, init="zero")),
                     "the interpreter runs this; flagging it would be a false alarm")


class VariableIndexStaysOut(unittest.TestCase):
  def test_a_variable_index_is_refused(self):
    with self.assertRaises(SmvUnsupported) as cm:
      model_of(VARIABLE_INDEX, init="zero")
    self.assertIn("plain variable", str(cm.exception))


if __name__ == "__main__":
  unittest.main()
