"""Structs, expanded to scalars — one variable per field.

Of the 97 example programs, 13 are blocked by structs alone. No field has a
struct type (the "nested" in `structs_nested.ja` is nested *call sites*, not
nested types), so this is the array story again: a struct variable becomes one
SMV variable per field, `p.x` names that variable, and a struct parameter binds
the caller's fields by reference exactly as an array does.

This first step covers structs whose fields are all scalars. Array fields and
arrays of structs are the next two.
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

DEF = "struct Point {\n    int x;\n    int y;\n};\n\n"

SCALAR = DEF + "procedure main()\n    Point p\n    p.x += 1\n    p.y += 2\n"
FIELD_SWAP = DEF + "procedure main()\n    Point p\n    p.x += 1\n    p.x <=> p.y\n"
BY_REF = (DEF + "procedure bump(Point q)\n    q.x += 1\n\n"
          "procedure main()\n    Point p\n    call bump(p)\n")
#: `structs_nested.ja`'s shape: a procedure passes its own struct formals onward.
ONWARD = (DEF + "procedure addv(Point a, Point b)\n    a.x += b.x\n    a.y += b.y\n\n"
          "procedure acc(Point s, Point d)\n    call addv(s, d)\n\n"
          "procedure main()\n    Point p\n    Point q\n    q.x += 1\n    call acc(p, q)\n")
#: Two formals bound to one struct is not an error by itself, as for arrays.
SAME_STRUCT = (DEF + "procedure addv(Point a, Point b)\n    a.x += b.y\n\n"
               "procedure main()\n    Point p\n    call addv(p, p)\n")


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


def interpreter_fails(src: str) -> bool:
  proc = subprocess.run([sys.executable, "-m", "jana_py.cli", "--std", "jana2014", "-s", "-"],
                        input=src, capture_output=True, text=True, cwd=ROOT)
  return proc.returncode != 0


class ExpansionTests(unittest.TestCase):
  def test_each_field_becomes_a_variable(self):
    self.assertEqual(declared(model_of(SCALAR, init="zero")), ["p_x", "p_y"])

  def test_a_field_reference_names_that_variable(self):
    model = model_of(SCALAR, init="zero")
    self.assertEqual(next_branches(model, "p_x"), ["(p_x + 1)"])
    self.assertEqual(next_branches(model, "p_y"), ["(p_y + 2)"])

  def test_fields_can_be_swapped(self):
    model = model_of(FIELD_SWAP, init="zero")
    self.assertEqual(next_branches(model, "p_x"), ["p_y"])
    self.assertEqual(next_branches(model, "p_y"), ["(p_x + 1)"])

  def test_a_struct_parameter_is_by_reference(self):
    model = model_of(BY_REF, init="zero")
    self.assertEqual(next_branches(model, "p_x"), ["(p_x + 1)"])

  def test_formals_passed_onward_still_resolve(self):
    # `structs_nested.ja`'s shape: the callee hands its own formals to a third
    # procedure, so the binding has to survive a second resolution.
    model = model_of(ONWARD, init="zero")
    self.assertEqual(next_branches(model, "p_x"), ["(p_x + (q_x + 1))"])


class AliasTests(unittest.TestCase):
  """The per-statement rule carries over: two formals on one struct is fine."""

  def test_two_formals_on_one_struct_is_not_itself_an_error(self):
    self.assertFalse(interpreter_fails(SAME_STRUCT))
    model = model_of(SAME_STRUCT, init="zero")
    self.assertNotIn(": 0;", model.split("next(pc) := case")[1].split("esac;")[0])

  def test_a_field_aliasing_itself_is_an_error(self):
    src = (DEF + "procedure addv(Point a, Point b)\n    a.x += b.x\n\n"
           "procedure main()\n    Point p\n    call addv(p, p)\n")
    self.assertTrue(interpreter_fails(src))
    self.assertIn(": 0;", model_of(src, init="zero").split("next(pc) := case")[1])


class StillRefusedTests(unittest.TestCase):
  def test_an_array_field_is_refused(self):
    src = ("struct Box {\n    int v[3];\n    int w;\n};\n\n"
           "procedure main()\n    Box b\n    b.w += 1\n")
    with self.assertRaises(SmvUnsupported):
      model_of(src, init="zero")

  def test_an_array_of_structs_is_refused(self):
    src = DEF + "procedure main()\n    Point p[2]\n    p[0].x += 1\n"
    with self.assertRaises(SmvUnsupported):
      model_of(src, init="zero")


@unittest.skipIf(BINARY is None, "nuXmv not installed")
class AgreementTests(unittest.TestCase):
  def test_the_model_checker_agrees_with_the_interpreter(self):
    for name, src in (("scalar", SCALAR), ("field-swap", FIELD_SWAP),
                      ("by-ref", BY_REF), ("onward", ONWARD),
                      ("same-struct", SAME_STRUCT)):
      with self.subTest(name):
        fails = interpreter_fails(src)
        result = nuxmv.check(model_of(src, init="zero"), binary=BINARY)
        self.assertEqual(result.status, "refuted" if fails else "proved",
                         result.output[-2000:])


if __name__ == "__main__":
  unittest.main()
