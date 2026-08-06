"""Arrays of rank > 1, flattened row-major.

An array is already a flat tuple of cell variables, so a second dimension needs
one new thing: the *shape*, kept beside the tuple so that `A[i][j]` can fold to
`i * cols + j` and so that each index can be bounds-checked against **its own**
dimension.  Flattening without the shape would accept `A[0][5]` on a 2x3 array,
whose flat offset 5 is perfectly in range.

The three shapes that appear in the corpus all reduce to this one, because
`_base_of` lifts the field selector out and leaves the indices in row-major
order whichever side of the field they were on:

    a.grid[i][j]     scalar struct, 2-D field      -> dims (2, 2)
    grid[i][j].y     2-D array of structs          -> dims (2, 2)
    g[i].v[j]        array of structs, array field -> dims (2, 3)

So one shape registry covers all of them, and the field-major layout that
arrays of structs already used is what makes the last line work.
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


def model_of(src: str, **kw) -> str:
  pt = preprocess.preprocess_text("<test>", src, None, "jana2014")
  program = parser_jana2014.parse_program("<test>", pt.text, pt.line_origins)
  return compile_to_smv(program, **kw)


def declared(model: str) -> list[str]:
  return re.findall(r"^  (\w+) : integer;", model, re.M)


def next_branches(model: str, var: str) -> list[str]:
  out, inside = [], False
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
        out.append(m.group(2))
  return out


def reaches_err(model: str) -> bool:
  return ": 0;" in model.split("next(pc) := case")[1].split("esac;")[0]


def interpreter_fails(src: str) -> bool:
  proc = subprocess.run([sys.executable, "-m", "jana_py.cli", "--std", "jana2014", "-s", "-"],
                        input=src, capture_output=True, text=True, cwd=ROOT)
  return proc.returncode != 0


PLAIN = "procedure main()\n    int A[2][3]\n    A[1][2] += 1\n    A[0][0] += 2\n"
DYN = ("procedure main()\n    int A[2][3]\n    int i\n    int j\n"
       "    i += 1\n    j += 2\n    A[i][j] += 5\n")
OOB = "procedure main()\n    int A[2][3]\n    A[0][5] += 1\n"
REF = ("procedure fill(int B[][])\n    B[1][0] += 1\n\n"
       "procedure main()\n    int A[2][3]\n    call fill(A)\n")


class PlainArrayTests(unittest.TestCase):
  def test_it_expands_row_major(self):
    self.assertEqual(declared(model_of(PLAIN, init="zero", arrays="expand")),
                     ["A_0_0", "A_0_1", "A_0_2", "A_1_0", "A_1_1", "A_1_2"])

  def test_constant_indices_name_the_cell(self):
    model = model_of(PLAIN, init="zero", arrays="expand")
    self.assertEqual(next_branches(model, "A_1_2"), ["(A_1_2 + 1)"])
    self.assertEqual(next_branches(model, "A_0_0"), ["(A_0_0 + 2)"])

  def test_a_variable_index_folds_to_one_offset(self):
    model = model_of(DYN, init="zero")
    self.assertIn("(((i + 1) * 3) + (j + 2))", model)

  def test_each_index_is_checked_against_its_own_dimension(self):
    model = model_of(DYN, init="zero")
    self.assertRegex(model, r"\(+i \+ 1\)+ < 2")
    self.assertRegex(model, r"\(+j \+ 2\)+ < 3")

  def test_an_index_in_range_of_the_flattening_is_still_out_of_bounds(self):
    # Flat offset 5 lands inside a 6-cell array; the *column* index does not.
    self.assertTrue(interpreter_fails(OOB))
    self.assertTrue(reaches_err(model_of(OOB, init="zero")))

  def test_it_passes_by_reference(self):
    model = model_of(REF, init="zero", arrays="expand")
    self.assertEqual(next_branches(model, "A_1_0"), ["(A_1_0 + 1)"])


BOXDEF = "struct Box {\n    int grid[2][2];\n    int w;\n};\n\n"
FIELD_2D = (BOXDEF + "procedure main()\n    Box a\n"
            "    a.grid[0][0] += 2\n    a.grid[1][1] += 4\n"
            "    a.grid[0][1] += a.grid[1][1]\n")

PDEF = "struct P {\n    int x;\n    int y;\n};\n\n"
GRID = (PDEF + "procedure main()\n    P grid[2][2]\n"
        "    grid[0][0].x += 1\n    grid[1][1].y += 4\n"
        "    grid[0][0].y += grid[1][1].y\n")

ROWDEF = "struct Row {\n    int v[3];\n    int sum;\n};\n\n"
ROWS = (ROWDEF + "procedure main()\n    Row g[2]\n"
        "    g[0].v[2] += 3\n    g[1].v[0] += 4\n"
        "    g[1].sum += g[0].v[2]\n")


class StructTests(unittest.TestCase):
  def test_a_two_dimensional_field(self):
    self.assertEqual(declared(model_of(FIELD_2D, init="zero", arrays="expand")),
                     ["a_grid_0_0", "a_grid_0_1", "a_grid_1_0", "a_grid_1_1", "a_w"])

  def test_a_two_dimensional_array_of_structs(self):
    # Field-major, so the shape belongs to the field's tuple.
    self.assertEqual(declared(model_of(GRID, init="zero", arrays="expand")),
                     ["grid_x_0_0", "grid_x_0_1", "grid_x_1_0", "grid_x_1_1",
                      "grid_y_0_0", "grid_y_0_1", "grid_y_1_0", "grid_y_1_1"])

  def test_an_array_field_inside_an_array_of_structs(self):
    # `g[i].v[j]`: the element index and the field index compose into one
    # 2 x 3 shape, which is why the field selector sitting between them is
    # harmless once `_base_of` lifts it out.
    self.assertEqual(declared(model_of(ROWS, init="zero", arrays="expand")),
                     ["g_v_0_0", "g_v_0_1", "g_v_0_2",
                      "g_v_1_0", "g_v_1_1", "g_v_1_2",
                      "g_sum_0", "g_sum_1"])

  def test_cross_reads_resolve(self):
    self.assertEqual(next_branches(model_of(ROWS, init="zero", arrays="expand"), "g_sum_1"),
                     ["(g_sum_1 + (g_v_0_2 + 3))"])


class StillRefusedTests(unittest.TestCase):
  def test_the_rank_must_match_the_argument(self):
    src = ("procedure fill(int B[])\n    B[0] += 1\n\n"
           "procedure main()\n    int A[2][3]\n    call fill(A)\n")
    with self.assertRaises(SmvUnsupported):
      model_of(src, init="zero")

  def test_a_partially_applied_index_is_refused(self):
    src = "procedure main()\n    int A[2][3]\n    int s\n    s += A[0]\n"
    with self.assertRaises(SmvUnsupported):
      model_of(src, init="zero")


class CorpusTests(unittest.TestCase):
  """The programs this unblocks, by name, so a regression is visible."""

  NOW_IN = ("structs_array_field_c.ja", "structs_array_field_arr_c.ja", "structs_grid_c.ja")

  def test_they_compile(self):
    for name in self.NOW_IN:
      with self.subTest(name):
        path = ROOT / "tests/jana2014/fixtures/examples" / name
        self.assertIn("INVARSPEC", model_of(path.read_text(encoding="utf-8"), init="zero"))


@unittest.skipIf(BINARY is None, "nuXmv not installed")
class AgreementTests(unittest.TestCase):
  def test_the_model_checker_agrees_with_the_interpreter(self):
    for name, src in (("plain", PLAIN), ("dynamic", DYN), ("out-of-bounds", OOB),
                      ("by-ref", REF), ("field-2d", FIELD_2D), ("grid", GRID),
                      ("rows", ROWS)):
      with self.subTest(name):
        fails = interpreter_fails(src)
        result = nuxmv.check(model_of(src, init="zero"), binary=BINARY)
        self.assertEqual(result.status, "refuted" if fails else "proved",
                         result.output[-2000:])


if __name__ == "__main__":
  unittest.main()
