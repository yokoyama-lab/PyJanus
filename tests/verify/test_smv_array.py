"""Arrays, expanded to scalars — declarations and constant indices.

Coverage is the checker's biggest limitation: of the 97 example programs, 8
compile today and **41 more are blocked by arrays alone** (31 by stacks, 13 by
structs). Expanding arrays is therefore what moves the number, and this file is
the first step of it: declarations become one SMV variable per element, and a
constant index names the element directly. Variable indices are the next step and
are still refused here.

An out-of-bounds constant index is **not** a translation gap, it is a program
that fails: PyJanus reports "Array index `[5]' was out of bounds (array size was
[3])". So it becomes an unconditional edge to ERR, exactly as an aliasing
violation does. Leaving it out would repeat the defect the swap check and the
modular modes just had — a model that proves a failing program safe.
"""

from __future__ import annotations

from pathlib import Path
import re
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from jana_py import nuxmv
from jana_py import parser_jana2014
from jana_py import preprocess
from jana_py.smv import SmvUnsupported
from jana_py.smv import compile_to_smv

BINARY = nuxmv.find_nuxmv()

FIXED = "procedure main()\n    int a[3]\n    a[1] += 2\n"
INITIALISED = "procedure main()\n    int b[2] = {7,8}\n    b[0] += 1\n"
OOB = "procedure main()\n    int a[3]\n    a[5] += 2\n"
DYNAMIC = "procedure main()\n    int a[3]\n    int i\n    a[i] += 2\n"
SWAP_CELLS = "procedure main()\n    int a[3]\n    a[0] += 1\n    a[0] <=> a[2]\n"


def model_of(src: str, **kw) -> str:
  pt = preprocess.preprocess_text("<test>", src, None, "jana2014")
  program = parser_jana2014.parse_program("<test>", pt.text, pt.line_origins)
  return compile_to_smv(program, **kw)


def declared_vars(model: str) -> list[str]:
  out = []
  for line in model.splitlines():
    m = re.match(r"\s*(\w+) : integer;", line)
    if m:
      out.append(m.group(1))
  return out


def next_branches(model: str, var: str) -> list[tuple[str, str]]:
  out: list[tuple[str, str]] = []
  inside = False
  for line in model.splitlines():
    stripped = line.strip()
    if stripped == f"next({var}) := case":
      inside = True
      continue
    if inside:
      if stripped == "esac;":
        break
      m = re.match(r"(.*?) : (.*);$", stripped)
      assert m is not None, stripped
      if m.group(1) != "TRUE":
        out.append((m.group(1), m.group(2)))
  return out


def has_err_edge(model: str) -> bool:
  inside = False
  for line in model.splitlines():
    if line.strip().startswith("next(pc) :="):
      inside = True
      continue
    if inside:
      if line.strip() == "esac;":
        return False
      if line.strip().endswith(": 0;"):
        return True
  return False


def interpreter_fails(src: str) -> bool:
  proc = subprocess.run([sys.executable, "-m", "jana_py.cli", "--std", "jana2014", "-s", "-"],
                        input=src, capture_output=True, text=True, cwd=ROOT)
  return proc.returncode != 0


class ReferenceBehaviourTests(unittest.TestCase):
  def test_in_bounds_runs(self):
    self.assertFalse(interpreter_fails(FIXED))

  def test_out_of_bounds_fails(self):
    self.assertTrue(interpreter_fails(OOB))


class ExpansionTests(unittest.TestCase):
  def test_a_declaration_becomes_one_variable_per_element(self):
    # `pc` is declared as a range, not an integer, so it is not in this list.
    self.assertEqual(declared_vars(model_of(FIXED, init="zero")),
                     ["a_0", "a_1", "a_2"])

  def test_a_constant_index_names_the_element(self):
    model = model_of(FIXED, init="zero")
    self.assertEqual([v for _, v in next_branches(model, "a_1")], ["(a_1 + 2)"])
    # the untouched elements get no next-state function at all
    self.assertNotIn("next(a_0) := case", model)
    self.assertNotIn("next(a_2) := case", model)

  def test_an_initialiser_lands_element_by_element(self):
    model = model_of(INITIALISED, init="zero")
    self.assertIn("init(b_0) := 7;", model)
    self.assertIn("init(b_1) := 8;", model)

  def test_cells_can_be_swapped(self):
    model = model_of(SWAP_CELLS, init="zero")
    self.assertEqual([v for _, v in next_branches(model, "a_0")], ["a_2"])
    self.assertEqual([v for _, v in next_branches(model, "a_2")], ["(a_0 + 1)"])


class OutOfBoundsTests(unittest.TestCase):
  """A constant index outside the array is a failing program, not a gap."""

  def test_it_gets_an_err_edge(self):
    self.assertTrue(has_err_edge(model_of(OOB, init="zero")))

  def test_an_in_bounds_program_gets_none(self):
    self.assertFalse(has_err_edge(model_of(FIXED, init="zero")))


DYN_READ = ("procedure main()\n    int a[3]\n    int i\n    int x\n"
            "    i += 1\n    x += a[i]\n")
DYN_READ_OOB = ("procedure main()\n    int a[3]\n    int i\n    int x\n"
                "    i += 5\n    x += a[i]\n")
DYN_READ_ONE = ("procedure main()\n    int a[1]\n    int i\n    int x\n"
                "    x += a[i]\n")
CELL_VS_DYN = ("procedure main()\n    int a[3]\n    int i\n    a[0] += a[i]\n")


class DynamicReadTests(unittest.TestCase):
  """`a[i]` reads through a `case` over the elements, guarded by the bounds.

  38 of the 41 array-blocked programs use a variable index, so this is the step
  that matters for coverage.  Out-of-range is a run-time error in PyJanus, so it
  is an obligation checked into ERR — not an assumption.
  """

  def test_the_read_is_a_case_over_the_elements(self):
    model = model_of(DYN_READ, init="zero")
    self.assertIn("(i + 1) = 0 : a_0", model)
    self.assertIn("(i + 1) = 1 : a_1", model)
    # the last element is the `TRUE` default rather than its own branch
    self.assertIn("TRUE : a_2", model)

  def test_the_bounds_are_checked_into_err(self):
    model = model_of(DYN_READ, init="zero")
    self.assertTrue(has_err_edge(model), "an out-of-range index must reach ERR")
    # `_iexpr` already parenthesises, so the operand may be nested; pin the
    # operand and the bound, not the number of brackets.
    self.assertRegex(model, r"\(+i \+ 1\)+ >= 0")
    self.assertRegex(model, r"\(+i \+ 1\)+ < 3")

  def test_a_one_element_array_needs_no_case(self):
    model = model_of(DYN_READ_ONE, init="zero")
    self.assertNotIn("case (i)", model)
    self.assertTrue(has_err_edge(model))

  def test_the_index_is_read_through_the_pending_map(self):
    # `i += 1` precedes the read, so the index term is the accumulated `(i + 1)`,
    # not the entry value — the large-block discipline of RevSmvBlock.v.
    self.assertIn("(i + 1)", model_of(DYN_READ, init="zero"))
    self.assertNotIn("case (i) = 0", model_of(DYN_READ, init="zero"))


class StillRefusedTests(unittest.TestCase):
  """What this step deliberately does not do yet."""

  def test_a_variable_index_write_is_refused(self):
    with self.assertRaises(SmvUnsupported):
      model_of(DYNAMIC, init="zero")

  def test_a_cell_against_a_variable_index_is_refused(self):
    # `a[0] += a[i]` is an error exactly when i = 0.  Answering "yes" would be a
    # false alarm and "no" would be unsound, so it is refused until the
    # index-precise aliasing check exists.
    with self.assertRaises(SmvUnsupported):
      model_of(CELL_VS_DYN, init="zero")

  def test_a_zero_length_array_is_refused(self):
    # Caught by the corpus check while landing this step: `int x[0]` is rejected
    # by PyJanus at the declaration ("Array size must be greater than or equal
    # to one"), so the program never runs.  An earlier version of the expansion
    # accepted it and emitted a model with no variables at all, which nuXmv
    # duly *proved* — a program that cannot start, certified safe.
    self.assertTrue(interpreter_fails("procedure main()\n    int x[0]\n    skip\n"))
    with self.assertRaises(SmvUnsupported):
      model_of("procedure main()\n    int x[0]\n    skip\n", init="zero")

  def test_a_whole_array_l_value_is_refused(self):
    with self.assertRaises(SmvUnsupported):
      model_of("procedure main()\n    int a[3]\n    int x\n    x += a\n", init="zero")


@unittest.skipIf(BINARY is None, "nuXmv not installed")
class AgreementTests(unittest.TestCase):
  def test_the_model_checker_agrees_with_the_interpreter(self):
    for name, src, fails in (("in-bounds", FIXED, False),
                             ("initialised", INITIALISED, False),
                             ("swap-cells", SWAP_CELLS, False),
                             ("out-of-bounds", OOB, True),
                             ("dynamic-read", DYN_READ, False),
                             ("dynamic-read-oob", DYN_READ_OOB, True)):
      with self.subTest(name):
        self.assertEqual(interpreter_fails(src), fails)
        result = nuxmv.check(model_of(src, init="zero"), binary=BINARY)
        self.assertEqual(result.status, "refuted" if fails else "proved",
                         result.output[-2000:])


if __name__ == "__main__":
  unittest.main()
