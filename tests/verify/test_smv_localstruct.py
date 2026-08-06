"""`local struct Box e = a … delocal struct Box e = a`.

A struct local is a **copy**: every field is bound from the initializer on
entry, and on exit every field has to match the exit expression again.  Both
halves of that are load-bearing and both were probed against the interpreter
first — changing the *local* in the body fails, and so does changing the
*source*, because the exit expression is re-evaluated after the body (the same
rule as a value argument, `test_smv_valuearg.py`).

Two things are deliberately **not** encoded:

* `local int t[2] = a`.  PyJanus does not run it — it raises a bare Python
  `TypeError` out of the interpreter — so there is no reference behaviour to
  match, and inventing one would make the model an authority on a program the
  implementation cannot execute.
* `local stack …`.  Five of the seven programs blocked by `non-scalar local`
  are stacks, which is the other wall entirely.

A `delocal` whose *type* disagrees with its `local` is a run-time error in
PyJanus, so it becomes an unconditional edge to ERR — the same treatment the
name mismatch already had.
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

DEF = "struct Box {\n    int v[2];\n    int w;\n};\n\n"
HEAD = DEF + "procedure main()\n    Box a\n    int s\n    a.w += 5\n    a.v[0] += 3\n"

OK = HEAD + ("    local struct Box e = a\n        s += e.w + e.v[0]\n"
             "    delocal struct Box e = a\n")
LOCAL_MOVED = HEAD + ("    local struct Box e = a\n        e.w += 1\n"
                      "    delocal struct Box e = a\n")
SOURCE_MOVED = HEAD + ("    local struct Box e = a\n        a.w += 1\n"
                       "    delocal struct Box e = a\n")
TYPE_MISMATCH = "procedure main()\n    local int x = 0\n    skip\n    delocal stack x = 0\n"


def model_of(src: str, **kw) -> str:
  pt = preprocess.preprocess_text("<test>", src, None, "jana2014")
  program = parser_jana2014.parse_program("<test>", pt.text, pt.line_origins)
  return compile_to_smv(program, **kw)


def declared(model: str) -> list[str]:
  return re.findall(r"^  (\w+) : integer;", model, re.M)


def reaches_err(model: str) -> bool:
  return ": 0;" in model.split("next(pc) := case")[1].split("esac;")[0]


def interpreter_fails(src: str) -> bool:
  proc = subprocess.run([sys.executable, "-m", "jana_py.cli", "--std", "jana2014", "-s", "-"],
                        input=src, capture_output=True, text=True, cwd=ROOT)
  return proc.returncode != 0


class InterpreterSemanticsTests(unittest.TestCase):
  def test_an_untouched_copy_is_fine(self):
    self.assertFalse(interpreter_fails(OK))

  def test_moving_the_local_is_the_error(self):
    self.assertTrue(interpreter_fails(LOCAL_MOVED))

  def test_moving_the_source_is_also_the_error(self):
    # i.e. the exit expression is re-evaluated after the body.
    self.assertTrue(interpreter_fails(SOURCE_MOVED))

  def test_a_type_mismatch_is_a_run_time_error(self):
    self.assertTrue(interpreter_fails(TYPE_MISMATCH))


class EncodingTests(unittest.TestCase):
  def test_the_copy_gets_its_own_variables(self):
    self.assertEqual(declared(model_of(OK, init="zero", arrays="expand")),
                     ["a_v_0", "a_v_1", "a_w", "s", "e_v_0", "e_v_1", "e_w"])

  def test_every_field_is_bound_and_checked(self):
    model = model_of(OK, init="zero", arrays="expand")
    for cell, src in (("e_w", "(a_w + 5)"), ("e_v_0", "(a_v_0 + 3)"), ("e_v_1", "a_v_1")):
      self.assertIn(f"{cell}) := case", model)
      self.assertIn(src, model)

  def test_a_type_mismatch_goes_straight_to_err(self):
    self.assertTrue(reaches_err(model_of(TYPE_MISMATCH, init="zero")))

  def test_an_array_local_is_still_refused(self):
    # PyJanus cannot run it, so there is nothing to be faithful to.
    src = ("procedure main()\n    int a[2]\n    int s\n    a[0] += 5\n"
           "    local int t[2] = a\n        s += t[0]\n    delocal int t[2] = a\n")
    with self.assertRaises(SmvUnsupported):
      model_of(src, init="zero")

  def test_a_stack_local_is_still_refused(self):
    src = "procedure main()\n    local stack g = nil\n    skip\n    delocal stack g = nil\n"
    with self.assertRaises(SmvUnsupported):
      model_of(src, init="zero")


class CorpusTests(unittest.TestCase):
  NOW_IN = ("structs_local_arr_c.ja", "structs_local_arr2d_c.ja")

  def test_they_compile(self):
    for name in self.NOW_IN:
      with self.subTest(name):
        path = ROOT / "tests/jana2014/fixtures/examples" / name
        self.assertIn("INVARSPEC", model_of(path.read_text(encoding="utf-8"), init="zero"))


@unittest.skipIf(BINARY is None, "nuXmv not installed")
class AgreementTests(unittest.TestCase):
  def test_the_model_checker_agrees_with_the_interpreter(self):
    cases = [("ok", OK), ("local-moved", LOCAL_MOVED), ("source-moved", SOURCE_MOVED),
             ("type-mismatch", TYPE_MISMATCH)]
    for name in CorpusTests.NOW_IN:
      cases.append((name, (ROOT / "tests/jana2014/fixtures/examples" / name)
                    .read_text(encoding="utf-8")))
    for name, src in cases:
      with self.subTest(name):
        fails = interpreter_fails(src)
        result = nuxmv.check(model_of(src, init="zero"), binary=BINARY)
        self.assertEqual(result.status, "refuted" if fails else "proved",
                         result.output[-2000:])


if __name__ == "__main__":
  unittest.main()
