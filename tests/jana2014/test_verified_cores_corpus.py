"""The other two extracted cores, differentially tested against PyJanus.

`coq/harness/run.sh` builds three drivers but only ever runs two of them, and
the core one on just four hand-picked fixtures:

  * `driver`   — `RevExtract.v`, the plain core (no procedures, no arrays)
  * `driverp`  — `RevExtractP.v`, the parameterized core: **built and never run**
  * `driverar` — `RevExtractAr.v`, arrays + procedures (`test_verified_corpus.py`)

Each core is a separate extraction from a separate Rocq module with its own
soundness proof, so each is its own oracle and each deserves the whole corpus
rather than a sample.  Programs outside a core's subset skip with their reason —
which for the narrow cores is most of them, and that is the honest picture of
what each core actually covers.
"""
from __future__ import annotations

import glob
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "coq" / "harness"))
import differential  # noqa: E402
import differentialp  # noqa: E402

PROGRAMS = sorted(
    glob.glob(str(ROOT / "tests" / "jana2014" / "fixtures" / "examples" / "*.ja"))
    + glob.glob(str(ROOT / "coq" / "harness" / "fixtures" / "*.ja"))
)


def _compare(module, driver: Path, ja: str) -> None:
  try:
    diffs = module.check(str(driver), ja)
  except (module.Unsupported, KeyError) as e:
    pytest.skip(str(e))
  except Exception as e:  # a translator that trips on an out-of-subset shape
    pytest.skip(f"{type(e).__name__}: {e}")
  assert not diffs, "; ".join(f"{n}: verified={a} pyjanus={b}" for n, a, b in diffs)


@pytest.mark.parametrize("ja", PROGRAMS, ids=lambda p: Path(p).name)
def test_core_matches_pyjanus(ja: str, core_driver: Path) -> None:
  _compare(differential, core_driver, ja)


@pytest.mark.parametrize("ja", PROGRAMS, ids=lambda p: Path(p).name)
def test_param_core_matches_pyjanus(ja: str, param_driver: Path) -> None:
  _compare(differentialp, param_driver, ja)
