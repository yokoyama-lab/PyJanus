"""End-to-end tests: compile a Janus program and let nuXmv decide it.

These are the tests that make the SMV back-end trustworthy — they check the
model against the *interpreter's* behaviour, not against itself.  For each
program the interpreter is run too, and the two must agree on whether a runtime
assertion is reachable.  Skipped when nuXmv is not installed.
"""

from __future__ import annotations

from pathlib import Path
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from jana_py import nuxmv
from jana_py import parser_jana2014
from jana_py import preprocess
from jana_py.smv import compile_to_smv

BINARY = nuxmv.find_nuxmv()


def model_of(src: str, **kw) -> str:
  pt = preprocess.preprocess_text("<test>", src, None, "jana2014")
  program = parser_jana2014.parse_program("<test>", pt.text, pt.line_origins)
  return compile_to_smv(program, **kw)


def interpreter_fails(src: str) -> bool:
  """True when PyJanus itself reports a runtime error on the zero store."""
  proc = subprocess.run([sys.executable, "-m", "jana_py.cli", "--std", "jana2014", "-s", "-"],
                        input=src, capture_output=True, text=True, cwd=ROOT)
  return proc.returncode != 0


@unittest.skipIf(BINARY is None, "nuXmv not installed")
class AgreementTests(unittest.TestCase):
  """The model checker and the interpreter must agree on the zero store."""

  FAILING = {
      "assert": "procedure main()\n    assert(0=1)\n",
      "if-exit": "procedure main()\n    int x\n"
                 "    if x = 1 then\n        skip\n    fi x = 0\n",
      "loop-entry": "procedure main()\n    int x\n    from x = 1\n    until x = 0\n",
      "delocal": "procedure main()\n"
                 "    local   int x = 0\n    skip\n    delocal int x = 1\n",
      "div-zero": "procedure main()\n    int x\n    x += 5 / 0\n",
  }

  PASSING = {
      "inc": "procedure main()\n    int x\n    x += 1\n",
      "swap": "procedure main()\n    int x\n    int y\n    x += 1\n    x <=> y\n",
      "local": "procedure main()\n    int x\n"
               "    local   int z = 1\n    x += z\n    delocal int z = 1\n",
      "if-ok": "procedure main()\n    int x\n"
               "    if x = 0 then\n        x += 1\n    fi x = 1\n",
  }

  def test_failing_programs_are_refuted(self):
    for name, src in self.FAILING.items():
      with self.subTest(name):
        self.assertTrue(interpreter_fails(src), "interpreter should reject it")
        result = nuxmv.check(model_of(src, init="zero"), binary=BINARY)
        self.assertEqual(result.status, "refuted", result.output[-2000:])

  def test_passing_programs_are_proved(self):
    for name, src in self.PASSING.items():
      with self.subTest(name):
        self.assertFalse(interpreter_fails(src), "interpreter should accept it")
        result = nuxmv.check(model_of(src, init="zero"), binary=BINARY)
        self.assertEqual(result.status, "proved", result.output[-2000:])


@unittest.skipIf(BINARY is None, "nuXmv not installed")
class TotalityTests(unittest.TestCase):
  """`init="any"` asks the stronger question: is it total on *every* store?"""

  def test_a_program_total_only_on_a_subdomain_is_refuted(self):
    # Fine from x = 0, but `fi x = 1` fails for every other starting value.
    src = "procedure main()\n    int x\n    if x = 0 then\n        x += 1\n    fi x = 1\n"
    self.assertEqual(nuxmv.check(model_of(src, init="zero"), binary=BINARY).status, "proved")
    result = nuxmv.check(model_of(src, init="any"), binary=BINARY)
    self.assertEqual(result.status, "refuted", result.output[-2000:])

  def test_a_precondition_recovers_the_proof(self):
    src = "procedure main()\n    int x\n    if x = 0 then\n        x += 1\n    fi x = 1\n"
    result = nuxmv.check(model_of(src, init="any", assume="x = 0"), binary=BINARY)
    self.assertEqual(result.status, "proved", result.output[-2000:])

  def test_the_counterexample_is_a_concrete_store(self):
    src = "procedure main()\n    int x\n    if x = 0 then\n        x += 1\n    fi x = 1\n"
    result = nuxmv.check(model_of(src, init="any"), binary=BINARY)
    refuted = [v for v in result.verdicts if v.status == "refuted"]
    self.assertTrue(refuted)
    self.assertIn("x", refuted[0].counterexample)


class CounterexampleParsingTests(unittest.TestCase):
  """The trace's first state *is* the deliverable, so it has to be complete.

  A counterexample under `init="any"` is a missing precondition, which is only
  useful if it names the variables that carry it.  nuXmv prints array elements
  as `d[0] = 3`; a name pattern that stops at the bracket drops every one of
  them.  Once arrays entered the fragment that was most of the input —
  `glaisher.ja` came back as five dead locals while its two arrays, the whole
  content of the precondition, went unmentioned.
  """

  #: Abridged from a real `--init any` run on `base_convert.ja`.
  TRACE = """-- invariant pc != 0  is false
-- as demonstrated by the following execution sequence
Trace Type: Counterexample
  -> State: 1.1 <-
    pc = 2
    d[0] = 0
    d[1] = -3
    n = -2027
    b = -10
  -> State: 1.2 <-
    pc = 0
"""

  def test_array_elements_are_part_of_the_store(self):
    store = nuxmv._parse(self.TRACE)[0].counterexample
    self.assertEqual(store, {"d[0]": 0, "d[1]": -3, "n": -2027, "b": -10})

  def test_the_location_is_still_excluded(self):
    self.assertNotIn("pc", nuxmv._parse(self.TRACE)[0].counterexample)


@unittest.skipIf(BINARY is None, "nuXmv not installed")
class FloorDivisionAgreementTests(unittest.TestCase):
  """nuXmv truncates, Janus floors: the encoding must side with Janus.

  Without the floor correction `-7 / 2` is `-3` in the model and `-4` in the
  interpreter, so this program would be proved safe while actually failing.
  """

  SOURCE = ("procedure main()\n"
            "    int x\n"
            "    int q\n"
            "    x -= 7\n"
            "    q += x / 2\n"
            "    if q = -4 then\n        skip\n    else\n        assert(0=1)\n    fi q = -4\n")

  def test_interpreter_and_model_agree_on_negative_division(self):
    self.assertFalse(interpreter_fails(self.SOURCE))
    result = nuxmv.check(model_of(self.SOURCE, init="zero"), binary=BINARY)
    self.assertEqual(result.status, "proved", result.output[-2000:])


if __name__ == "__main__":
  unittest.main()
