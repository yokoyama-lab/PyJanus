"""Pin `smv.py`'s division macro to the shape proved correct in Rocq.

`coq/RevSmvExpr.v` proves

    mfdiv_correct : y <> 0 -> ⟦mfdiv a b⟧ = ⟦a⟧ / ⟦b⟧      (Rocq's `/` floors)

for the term `mfdiv` that transcribes `_div_defines`, where the model of nuXmv's
`/` is `Z.quot` — truncation toward zero, which is what nuXmv actually does and
what Janus does *not*. The theorem is only about the compiler if the compiler
still emits that shape, so these tests read the emitted DEFINEs back and check
two things:

* the four macros have exactly the verified structure (`_pin_shape`), and
* interpreting them with *truncating* division reproduces Python's `//` and `%`
  on a grid covering all four sign combinations and both boundaries
  (`_evaluate`).

The second is the executable mirror of `mfdiv_correct` / `mfmod_correct`: the
proof says the formula is right for every integer, the test says the *string the
compiler emits* is that formula. `test_smv_nuxmv.py` closes the loop from the
other end by having nuXmv itself agree with the interpreter.
"""

from __future__ import annotations

from pathlib import Path
import re
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from jana_py import parser_jana2014
from jana_py import preprocess
from jana_py.smv import compile_to_smv

SOURCE = ("procedure main()\n"
          "    int x\n    int y\n    int z\n"
          "    x += y / z\n")

MOD_SOURCE = ("procedure main()\n"
              "    int x\n    int y\n    int z\n"
              "    x += y % z\n")

#: The four DEFINEs, as `coq/RevSmvExpr.v` models them:
#:   mtq a b   = case b = 0 : 0; TRUE : a / b; esac
#:   mtr a b   = a - b * mtq
#:   mfdiv a b = case tr = 0 : tq; (tr < 0) <-> (b < 0) : tq; TRUE : tq - 1; esac
#:   mfmod a b = a - b * mfdiv
_SHAPES = {
    "tq": r"case \((?P<b>[^)]+)\) = 0 : 0; TRUE : \((?P<a>[^)]+)\) / \((?P=b)\); esac",
    "tr": r"\((?P<a>[^)]+)\) - \((?P<b>[^)]+)\) \* __tq(?P<i>\d+)",
    "fq": r"case __tr(?P<i>\d+) = 0 : __tq(?P=i); "
          r"\(__tr(?P=i) < 0\) <-> \(\((?P<b>[^)]+)\) < 0\) : __tq(?P=i); "
          r"TRUE : __tq(?P=i) - 1; esac",
    "fr": r"\((?P<a>[^)]+)\) - \((?P<b>[^)]+)\) \* __fq(?P<i>\d+)",
}


def defines(src: str) -> dict[str, str]:
  """The `__tq0` / `__tr0` / `__fq0` / `__fr0` bodies of the emitted model."""
  pt = preprocess.preprocess_text("<test>", src, None, "jana2014")
  program = parser_jana2014.parse_program("<test>", pt.text, pt.line_origins)
  model = compile_to_smv(program, init="any")
  out: dict[str, str] = {}
  for line in model.splitlines():
    m = re.match(r"\s*__(tq|tr|fq|fr)\d+ := (.*);\s*$", line)
    if m:
      out[m.group(1)] = m.group(2)
  return out


def _trunc_div(a: int, b: int) -> int:
  """nuXmv's `/`: truncation toward zero, unlike Python's `//`."""
  q = abs(a) // abs(b)
  return q if (a < 0) == (b < 0) else -q


def _evaluate(a: int, b: int) -> tuple[int, int]:
  """The emitted macro, read with nuXmv's semantics."""
  tq = 0 if b == 0 else _trunc_div(a, b)
  tr = a - b * tq
  fq = tq if tr == 0 else (tq if (tr < 0) == (b < 0) else tq - 1)
  fr = a - b * fq
  return fq, fr


GRID = [-97, -8, -7, -3, -2, -1, 0, 1, 2, 3, 7, 8, 97]


class ShapeTests(unittest.TestCase):
  """The compiler still emits the term the Rocq proof is about."""

  def test_all_four_defines_are_emitted(self):
    self.assertEqual(set(defines(SOURCE)), {"tq", "tr", "fq", "fr"})

  def test_each_define_has_the_verified_shape(self):
    d = defines(SOURCE)
    for name, pattern in _SHAPES.items():
      with self.subTest(name):
        self.assertRegex(d[name], f"^{pattern}$")

  def test_the_operands_are_the_source_ones(self):
    d = defines(SOURCE)
    m = re.match(f"^{_SHAPES['tq']}$", d["tq"])
    assert m is not None
    self.assertEqual(m.group("a"), "y")
    self.assertEqual(m.group("b"), "z")

  def test_modulo_reuses_the_same_macro(self):
    # `%` is derived from the floor quotient, not emitted independently.
    self.assertEqual(set(defines(MOD_SOURCE)), {"tq", "tr", "fq", "fr"})

  def test_the_naive_translation_would_differ(self):
    # The reason the macro exists at all: nuXmv's `/` is not Janus's.
    self.assertEqual(_trunc_div(-7, 2), -3)
    self.assertEqual(-7 // 2, -4)


class ValueTests(unittest.TestCase):
  """...and read with nuXmv's semantics it computes Python's `//` and `%`.

  This is `mfdiv_correct` / `mfmod_correct` executed rather than proved; the
  proof covers every integer, this covers the emitted text.
  """

  def test_quotient_matches_python(self):
    for a in GRID:
      for b in GRID:
        if b == 0:
          continue
        with self.subTest(a=a, b=b):
          self.assertEqual(_evaluate(a, b)[0], a // b)

  def test_remainder_matches_python(self):
    for a in GRID:
      for b in GRID:
        if b == 0:
          continue
        with self.subTest(a=a, b=b):
          self.assertEqual(_evaluate(a, b)[1], a % b)

  def test_the_divisor_zero_guard_keeps_the_macro_total(self):
    # The guard exists so the SMT engine never sees a division by zero in
    # states the ERR edge excludes anyway; the value there is irrelevant.
    self.assertEqual(_evaluate(5, 0), (0, 5))


if __name__ == "__main__":
  unittest.main()
