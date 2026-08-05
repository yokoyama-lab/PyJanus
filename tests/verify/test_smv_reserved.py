"""Identifiers nuXmv reserves, and the silence that hid them.

`A`, `T`, `K` and friends are temporal/epistemic operators in nuXmv's logic, so
a Janus variable with one of those names produces a model the tool refuses to
read.  Two corpus programs were in exactly that state — `knapsack.ja` declares
`K` and `injective_bwt_inverse.ja` declares `T` — and both were reported as
`unknown`, indistinguishable from "IC3 ran out of time".  They had never been
checked at all.

So there are two fixes here and the second matters more than the first:

1. the reserved set has to cover what nuXmv actually reserves (determined by
   probing the binary, not by reading a grammar);
2. a model the tool cannot *parse* must not be reported as an undecided
   verification.  Silence about a broken question reads as a hard question.
"""

from __future__ import annotations

from pathlib import Path
import re
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from jana_py import nuxmv
from jana_py import parser_jana2014
from jana_py import preprocess
from jana_py.smv import _SMV_RESERVED
from jana_py.smv import compile_to_smv

BINARY = nuxmv.find_nuxmv()

#: Rejected by nuXmv 2.2.0 when used as a variable name.  Probed, not guessed:
#: `K` is not in NuSMV's published grammar but nuXmv reserves it.
PROBED = ("A E F G H K O S T U V X Y Z EX AX EF AF EG AG BU EBF ABF EBG ABG "
          "count toint bool floor sizeof of ISA COMPUTE PSLSPEC MDEFINE "
          "CONSTARRAY signed unsigned extend resize MIN MAX").split()


def model_of(src: str, **kw) -> str:
  pt = preprocess.preprocess_text("<test>", src, None, "jana2014")
  program = parser_jana2014.parse_program("<test>", pt.text, pt.line_origins)
  return compile_to_smv(program, **kw)


class ReservedSetTests(unittest.TestCase):
  def test_every_probed_name_is_reserved(self):
    self.assertEqual([n for n in PROBED if n not in _SMV_RESERVED], [])

  def test_a_variable_with_a_reserved_name_is_renamed(self):
    model = model_of("procedure main()\n    int A\n    A += 1\n", init="zero")
    self.assertNotIn("\n  A : integer;", model)
    self.assertIn("\n  A_ : integer;", model)

  def test_an_array_with_a_reserved_name_is_renamed(self):
    model = model_of("procedure main()\n    int T[2]\n    T[0] += 1\n", init="zero")
    self.assertIn("\n  T_ : array 0..1 of integer;", model)


class MalformedModelTests(unittest.TestCase):
  """A model the tool cannot read is not an undecided verification."""

  BROKEN = ("MODULE main\nVAR\n  pc : 0..1;\n  A : integer;\n"
            "ASSIGN\n  init(pc) := 0;\n\nINVARSPEC pc != 1\n")

  @unittest.skipIf(BINARY is None, "nuXmv not installed")
  def test_it_is_flagged_rather_than_called_unknown(self):
    result = nuxmv.check(self.BROKEN, binary=BINARY)
    self.assertTrue(result.malformed)
    self.assertEqual(result.status, "model-error")

  @unittest.skipIf(BINARY is None, "nuXmv not installed")
  def test_a_good_model_is_not_flagged(self):
    good = model_of("procedure main()\n    int x\n    x += 1\n", init="zero")
    result = nuxmv.check(good, binary=BINARY)
    self.assertFalse(result.malformed)
    self.assertEqual(result.status, "proved")


@unittest.skipIf(BINARY is None, "nuXmv not installed")
class CorpusTests(unittest.TestCase):
  """The two programs that were never actually checked."""

  def test_they_are_now_readable(self):
    for name in ("knapsack.ja", "injective_bwt_inverse.ja"):
      with self.subTest(name):
        path = ROOT / "tests/jana2014/fixtures/examples" / name
        model = model_of(path.read_text(encoding="utf-8"), init="zero", style="assign")
        result = nuxmv.check(model, timeout=30, binary=BINARY)
        self.assertFalse(result.malformed, result.output[-1500:])

  def test_no_corpus_model_is_malformed(self):
    # The whole point: a spurious `unknown` is invisible unless something looks.
    for path in sorted((ROOT / "tests/jana2014/fixtures/examples").glob("*.ja")):
      src = path.read_text(encoding="utf-8")
      try:
        model = model_of(src, init="zero", style="assign")
      except Exception:
        continue  # outside the fragment, or not parseable: not this test's job
      with self.subTest(path.name):
        result = nuxmv.check(model, timeout=5, binary=BINARY)
        self.assertFalse(result.malformed,
                         re.sub(r"\s+", " ", result.output)[-500:])


if __name__ == "__main__":
  unittest.main()
