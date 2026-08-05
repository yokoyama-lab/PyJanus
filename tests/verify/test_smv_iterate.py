"""`iterate int i = a by s to b … end`, and its C-style twin `for`.

A counted loop is not `from`/`until` in disguise: a `from` loop runs its `do`
part **at least once**, and `iterate int i = 0 to -1` runs its body **zero**
times.  So this is built as a CFG directly rather than rewritten into another
statement — head, guarded body, increment, back edge.

Everything below was probed against the interpreter before it was encoded:

* `iterate i = 0 to 2` runs three times — the bound is `end + step`, not `end`.
  The C-style `for (i < end)` is exclusive and stops at `end`.
* `iterate i = 0 to -1` runs zero times.
* the loop variable **shadows** an outer one of the same name and is dropped
  afterwards;
* `step` and the stop value are evaluated **once, on entry**.  A body that
  permanently moves the variable the bound mentions does not change the trip
  count, so both have to be frozen into their own variables — re-reading the
  expression after the body would be wrong.

Not modelled, and not modellable here: a body that writes the loop variable can
make the counter step over the stop value, and PyJanus then runs forever.  The
model simply never reaches the exit, which is the documented meaning of a
proof (§6: non-termination is not an assertion failure).
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
from jana_py import parser_janus2026
from jana_py import preprocess
from jana_py.smv import SmvUnsupported
from jana_py.smv import compile_to_smv

BINARY = nuxmv.find_nuxmv()


def model_of(src: str, std: str = "jana2014", **kw) -> str:
  parse = (parser_jana2014 if std == "jana2014" else parser_janus2026).parse_program
  pt = preprocess.preprocess_text("<test>", src, None, std)
  return compile_to_smv(parse("<test>", pt.text, pt.line_origins), **kw)


def store_of(src: str, std: str = "jana2014") -> str:
  proc = subprocess.run([sys.executable, "-m", "jana_py.cli", "--std", std, "-s", "-"],
                        input=src, capture_output=True, text=True, cwd=ROOT, timeout=60)
  return proc.stdout.strip().splitlines()[-1] if proc.returncode == 0 else "FAILED"


THREE = "procedure main()\n    int s\n    iterate int i = 0 to 2\n        s += 1\n    end\n"
NONE = "procedure main()\n    int s\n    iterate int i = 0 to -1\n        s += 1\n    end\n"
STEPPED = "procedure main()\n    int s\n    iterate int i = 0 by 2 to 4\n        s += 1\n    end\n"
READS_I = "procedure main()\n    int s\n    iterate int i = 1 to 3\n        s += i\n    end\n"
SHADOWS = ("procedure main()\n    int i\n    int s\n    i += 9\n"
           "    iterate int i = 0 to 2\n        s += 1\n    end\n    s += i\n")
#: The body moves `n` for good; the trip count must not follow it.
FROZEN = ("procedure main()\n    int n\n    int s\n    n += 2\n"
          "    iterate int i = 0 to n\n        s += 1\n        n += 1\n    end\n")
UNCALL = ("procedure p(int s)\n    iterate int i = 1 to 3\n        s += i\n    end\n\n"
          "procedure main()\n    int s\n    s += 6\n    uncall p(s)\n")
EXCLUSIVE = ("void main() {\n    int s;\n"
             "    for (int i = 0; i < 3; i += 1) {\n        s += 1;\n    }\n}\n")


class InterpreterSemanticsTests(unittest.TestCase):
  """The trip counts the encoding has to reproduce."""

  def test_the_bound_is_inclusive_for_iterate(self):
    self.assertEqual(store_of(THREE), "s = 3")

  def test_it_can_run_zero_times(self):
    self.assertEqual(store_of(NONE), "s = 0")

  def test_the_step_is_honoured(self):
    self.assertEqual(store_of(STEPPED), "s = 3")

  def test_the_loop_variable_is_readable_and_shadowing(self):
    self.assertEqual(store_of(READS_I), "s = 6")
    self.assertEqual(store_of(SHADOWS), "s = 12")

  def test_the_bound_is_frozen_on_entry(self):
    self.assertEqual(store_of(FROZEN), "s = 3")

  def test_the_c_style_form_is_exclusive(self):
    self.assertEqual(store_of(EXCLUSIVE, std="janus2026"), "s = 3")


class EncodingTests(unittest.TestCase):
  def test_the_stop_value_gets_its_own_variable(self):
    # Frozen, so the body cannot move it.  `n + 2` is the entry value of `n`.
    model = model_of(FROZEN, init="zero")
    self.assertIn("i_stop", model)
    self.assertIn("((n + 2) + 1)", model)

  def test_the_loop_variable_shadows_rather_than_reuses(self):
    model = model_of(SHADOWS, init="zero")
    self.assertIn("\n  i : integer;", model)     # the outer one, untouched
    self.assertIn("\n  i__1 : integer;", model)  # the loop's own, renamed
    self.assertIn("pc = 2 : (i + 9);", model)     # the outer one still moves

  def test_a_zero_trip_loop_still_has_an_exit_edge(self):
    # The guard is `i != stop`, so the body is skipped rather than entered once.
    self.assertIn("!(", model_of(NONE, init="zero"))


class CorpusTests(unittest.TestCase):
  """`iterate` blocked 11 programs; it is the *only* blocker of one of them.

  Eight of the other ten stop at `^=` next, which is why this item moved the
  coverage number by 3 and not by 11.  Asserting that they get *past* `iterate` is still
  worth a test — it is the difference between "encoded" and "encoded and
  reachable".
  """

  #: `iterate` was their last blocker.
  NOW_IN = ("injective_arithmetic.ja", "injective_lehmer.ja", "structs_local.ja")
  #: Past `iterate`, stopped by something else (`^=`, or a cell argument).
  STILL_OUT = ("gray_code.ja", "gray_code_roundtrip.ja", "injective_ca_rule90.ja",
               "injective_iterate.ja", "reversible_ca_ring.ja",
               "reversible_ca_rule90.ja", "reversible_gates.ja",
               "structs_array_param.ja")

  def test_they_compile(self):
    for name in self.NOW_IN:
      with self.subTest(name):
        path = ROOT / "tests/jana2014/fixtures/examples" / name
        self.assertIn("INVARSPEC", model_of(path.read_text(encoding="utf-8"), init="zero"))

  def test_the_others_are_no_longer_blocked_by_iterate(self):
    for name in self.STILL_OUT:
      with self.subTest(name):
        path = ROOT / "tests/jana2014/fixtures/examples" / name
        with self.assertRaises(SmvUnsupported) as caught:
          model_of(path.read_text(encoding="utf-8"), init="zero")
        self.assertNotIn("IterateStmt", str(caught.exception))


@unittest.skipIf(BINARY is None, "nuXmv not installed")
class AgreementTests(unittest.TestCase):
  def test_the_model_checker_agrees_with_the_interpreter(self):
    for name, src, std in (("three", THREE, "jana2014"), ("none", NONE, "jana2014"),
                           ("stepped", STEPPED, "jana2014"),
                           ("reads-i", READS_I, "jana2014"),
                           ("shadows", SHADOWS, "jana2014"),
                           ("frozen", FROZEN, "jana2014"),
                           ("uncall", UNCALL, "jana2014"),
                           ("exclusive", EXCLUSIVE, "janus2026")):
      with self.subTest(name):
        fails = store_of(src, std) == "FAILED"
        result = nuxmv.check(model_of(src, std, init="zero"), binary=BINARY)
        self.assertEqual(result.status, "refuted" if fails else "proved",
                         result.output[-2000:])


if __name__ == "__main__":
  unittest.main()
