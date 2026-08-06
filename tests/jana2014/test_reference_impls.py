"""Check each example against an independent Python implementation.

The other corpus tests all run the same Janus source a second way -- backwards,
through the C++ back-end, through an extracted Coq interpreter -- so they catch
a back-end that disagrees and nothing else. A program that computes the wrong
thing agrees with itself perfectly.

`tests/jana2014/reference/<name>.py` is the second opinion: the algorithm
written again in Python, from what it *is* rather than from what the Janus says.
Its `expected()` returns the store values the program must end with, and this
test compares them key by key.

A program with no reference module skips, so the directory can be filled in a
few files at a time. `tools/check_corpus_meta.py report` counts the coverage.
"""

from __future__ import annotations

import glob
import importlib.util
import sys
import unittest
from pathlib import Path
from typing import Any

import pytest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))

from check_corpus_meta import is_trivial, observe, parse_store  # noqa: E402

EXAMPLES = sorted(glob.glob(str(ROOT / "tests" / "jana2014" / "fixtures" / "examples" / "*.ja")))
REFERENCE = Path(__file__).resolve().parent / "reference"


def load_reference(stem: str):
  """Import reference/<stem>.py, or return None if there isn't one."""
  path = REFERENCE / f"{stem}.py"
  if not path.exists():
    return None
  # Modules named `_*` are shared helpers (an AVL tree, a bit-vector) that the
  # references import by plain name, so the directory has to be importable.
  if str(REFERENCE) not in sys.path:
    sys.path.insert(0, str(REFERENCE))
  spec = importlib.util.spec_from_file_location(f"_reference_{stem}", path)
  module = importlib.util.module_from_spec(spec)
  spec.loader.exec_module(module)
  return module


def describe(value: Any) -> str:
  text = repr(value)
  return text if len(text) <= 300 else text[:300] + " ..."


@pytest.mark.parametrize("ja", EXAMPLES, ids=lambda p: Path(p).name)
def test_every_surviving_value_is_accounted_for(ja: str) -> None:
  """Nothing may be left in the store that is neither answer nor declared garbage.

  `expected()` says what the algorithm determines; `GARBAGE` names the history
  the reversible encoding has to keep. Between them they must cover everything
  the run leaves behind, so a value nobody claims becomes a question rather than
  a detail. A `PARTIAL` module is excused: by construction it does not predict
  part of its own answer.
  """
  path = Path(ja)
  module = load_reference(path.stem)
  if getattr(module, "PARTIAL", None):
    pytest.skip(f"partial reference: {module.PARTIAL}")
  _, store_lines = observe(path)
  store = parse_store(store_lines)
  claimed = set(module.expected()) | set(module.GARBAGE)
  orphans = sorted(name for name, value in store.items()
                   if not is_trivial(value) and name not in claimed)
  assert not orphans, (
    f"{path.name} leaves {', '.join(orphans)}, which the reference neither "
    f"predicts nor declares garbage")


@pytest.mark.parametrize("ja", EXAMPLES, ids=lambda p: Path(p).name)
def test_garbage_decides_the_filename(ja: str) -> None:
  """Every example says in its name whether it leaves garbage: `_g` or `_c`.

  The verdict comes from the reference rather than from the program's own
  header: `GARBAGE` is decided from the algorithm, and whether any of it
  actually survives is decided by running the program. Naming every file one way
  or the other -- rather than marking only the dirty ones -- means a file that
  nobody has classified cannot pass as clean.
  """
  path = Path(ja)
  module = load_reference(path.stem)
  _, store_lines = observe(path)
  store = parse_store(store_lines)
  left = sorted(name for name in module.GARBAGE
                if name in store and not is_trivial(store[name]))
  stem, suffix = path.stem[:-2], path.stem[-2:]
  assert suffix in ("_g", "_c"), (
    f"{path.name} must end in `_g` (leaves garbage) or `_c` (clean)")
  if left and suffix != "_g":
    raise AssertionError(
      f"{path.name} leaves garbage ({', '.join(left)}): rename to {stem}_g.ja")
  if not left and suffix != "_c":
    raise AssertionError(f"{path.name} leaves no garbage: rename to {stem}_c.ja")


@pytest.mark.parametrize("ja", EXAMPLES, ids=lambda p: Path(p).name)
def test_reference_agrees(ja: str) -> None:
  path = Path(ja)
  module = load_reference(path.stem)
  if module is None:
    pytest.skip("no reference implementation yet")

  _, store_lines = observe(path)
  store = parse_store(store_lines)
  expected = module.expected()
  assert expected, f"{path.name}: expected() returned nothing to compare"

  missing = [name for name in expected if name not in store]
  assert not missing, (
    f"{path.name}: reference names {', '.join(missing)}, which the final store "
    f"does not have (it has: {', '.join(store) or 'nothing'})")

  wrong = [
    f"{name}: reference says {describe(want)}, the program leaves {describe(store[name])}"
    for name, want in expected.items() if store[name] != want
  ]
  assert not wrong, f"{path.name} disagrees with its reference implementation:\n  " + "\n  ".join(wrong)


class ReferenceHygieneTests(unittest.TestCase):
  """The references are only worth having if they are actually independent."""

  def _modules(self) -> list[Path]:
    return sorted(p for p in REFERENCE.glob("*.py") if not p.name.startswith("_"))

  def test_no_reference_reaches_into_the_implementation(self) -> None:
    # Importing jana_py, running the interpreter, or reading a file would make
    # the "second opinion" a rephrasing of the first. Prose may name the .ja
    # freely; what is checked is the code.
    forbidden = ("jana_py", "subprocess", "open(", "read_text", "Path(", "__file__")
    for path in self._modules():
      code = "\n".join(
        line for line in path.read_text().splitlines()
        if not line.lstrip().startswith(("#", '"""', "'''"))
      )
      for name in forbidden:
        self.assertNotIn(name, code, f"{path.name} uses {name}")

  def test_every_reference_names_a_real_example(self) -> None:
    stems = {Path(ja).stem for ja in EXAMPLES}
    for path in self._modules():
      self.assertIn(path.stem, stems, f"{path.name} matches no example")

  def test_every_reference_defines_expected(self) -> None:
    for path in self._modules():
      module = load_reference(path.stem)
      self.assertTrue(callable(getattr(module, "expected", None)), f"{path.name} has no expected()")

  def test_every_example_has_a_reference(self) -> None:
    stems = {Path(ja).stem for ja in EXAMPLES}
    covered = {path.stem for path in self._modules()}
    self.assertEqual(stems - covered, set(), "examples with no reference implementation")

  def test_the_partial_references_are_the_declared_ones(self) -> None:
    # A reference that cannot predict part of the answer says so in `PARTIAL`,
    # so the gaps stay countable instead of dissolving into prose. Leaving
    # *garbage* unasserted is by design and is not a gap.
    partial = {path.stem: getattr(load_reference(path.stem), "PARTIAL", None)
               for path in self._modules()}
    self.assertEqual(
      sorted(stem for stem, reason in partial.items() if reason),
      ["adaptive_huffman_c", "binary_heap_g", "matrixmult_c", "matrixmult_v1_c", "ppm_lite_c"])


if __name__ == "__main__":
  unittest.main()
