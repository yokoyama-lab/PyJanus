"""Corpus-wide differential test: the *verified* (extracted) interpreter vs. PyJanus.

The extracted OCaml interpreter (`run`, proved sound in `coq/RevExtractAr.v`) is
run on every example/fixture and its final store compared to PyJanus.  The two
implementations share nothing — one is extracted from a machine-checked Rocq
development, the other is hand-written Python — so agreeing on the whole corpus
is evidence rather than a tautology.

The driver binary is built on demand by the `verified_driver` fixture
(`tests/conftest.py`): absent `rocq`/`ocamlc` the tests skip, and if those are
present but the build fails they fail loudly rather than skipping quietly.
Programs outside the verified subset skip with their reason.
"""
from __future__ import annotations

import glob
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "coq" / "harness"))
import differentialar  # noqa: E402

PROGRAMS = sorted(
    glob.glob(str(ROOT / "tests" / "jana2014" / "fixtures" / "examples" / "*.ja"))
    + glob.glob(str(ROOT / "coq" / "harness" / "fixtures" / "*.ja"))
)


@pytest.mark.parametrize("ja", PROGRAMS, ids=lambda p: Path(p).name)
def test_verified_matches_pyjanus(ja: str, verified_driver: Path) -> None:
  try:
    diffs = differentialar.check(str(verified_driver), ja)
  except (differentialar.Unsupported, KeyError) as e:
    pytest.skip(str(e))
  assert not diffs, "; ".join(f"{n}: verified={a} pyjanus={b}" for n, a, b in diffs)
