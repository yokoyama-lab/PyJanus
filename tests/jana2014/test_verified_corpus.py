"""Corpus-wide differential test: the *verified* (extracted) interpreter vs. PyJanus.

The extracted OCaml interpreter (`run`, proved sound in `coq/RevExtractAr.v`) is
run on every example/fixture and its final store compared to PyJanus.  This needs
the extracted driver binary, built by `coq/harness/run.sh` (rocq + ocamlc); when
it is absent (e.g. a plain checkout or CI without the Coq toolchain) the test
skips.  Programs outside the verified subset skip with their reason.
"""
from __future__ import annotations

import glob
import os
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "coq" / "harness"))
import differentialar  # noqa: E402

DRIVER = ROOT / "coq" / "harness" / "driverar"
PROGRAMS = sorted(
    glob.glob(str(ROOT / "tests" / "jana2014" / "fixtures" / "examples" / "*.ja"))
    + glob.glob(str(ROOT / "coq" / "harness" / "fixtures" / "*.ja"))
)


@pytest.mark.skipif(not DRIVER.exists(),
                    reason="extracted driver not built (run coq/harness/run.sh)")
@pytest.mark.parametrize("ja", PROGRAMS, ids=lambda p: Path(p).name)
def test_verified_matches_pyjanus(ja: str) -> None:
  # The harness shells out to `python3 -m jana_py.cli`; jana_py is dependency-free,
  # so making it importable to that subprocess is all that is needed.
  os.environ["PYTHONPATH"] = str(ROOT) + os.pathsep + os.environ.get("PYTHONPATH", "")
  try:
    diffs = differentialar.check(str(DRIVER), ja)
  except (differentialar.Unsupported, KeyError) as e:
    pytest.skip(str(e))
  assert not diffs, "; ".join(f"{n}: verified={a} pyjanus={b}" for n, a, b in diffs)
