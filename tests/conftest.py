"""Session fixtures that build the Coq-extracted interpreters on demand.

Several tests compare PyJanus against interpreters extracted from the Rocq
development — the whole point being that the two implementations are independent
(extracted Coq vs. hand-written Python), so agreement on every test program is
evidence and not a tautology.  Those interpreters need `rocq` and `ocamlc`.

Until now the tests only ran if you had remembered to run `coq/harness/run.sh`
and `coq/vjanus/build.sh` first.  Forgetting meant ~350 tests skipped while the
suite still reported green: the check silently had not happened.  A skip is the
right answer when the toolchain is genuinely absent, and the wrong answer when
it is present and the build merely was not done.

So the fixtures below build what they need, once per session, and separate the
two cases a bare `skipif(not binary.exists())` conflated:

* toolchain absent                        -> skip, with the reason
* toolchain present, build fails          -> **fail**, with the build's stderr
* toolchain present, build succeeds       -> run the comparison

Set `PYJANUS_SKIP_VERIFIED=1` to force the skip regardless (useful when the Rocq
side is mid-edit and you only want the Python suite).
"""

from __future__ import annotations

import os
import shutil
import subprocess
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
COQ = ROOT / "coq"
HARNESS = COQ / "harness"

#: driver name -> (extraction source, extracted module, driver source)
_DRIVERS = {
    "driver": ("RevExtract.v", "janus_verified", "harness/driver.ml"),
    "driverp": ("RevExtractP.v", "janus_param", "harness/driverp.ml"),
    "driverar": ("RevExtractAr.v", "janus_arr", "harness/driverar.ml"),
}


def _tool(env_var: str, name: str) -> str | None:
  override = os.environ.get(env_var)
  if override:
    return override if Path(override).exists() else None
  return shutil.which(name)


@pytest.fixture(scope="session")
def verified_toolchain() -> tuple[str, str]:
  """`(rocq, ocamlc)`, or skip the test when either is missing."""
  if os.environ.get("PYJANUS_SKIP_VERIFIED"):
    pytest.skip("PYJANUS_SKIP_VERIFIED is set")
  rocq, ocamlc = _tool("ROCQ", "rocq"), _tool("OCAMLC", "ocamlc")
  missing = [n for n, t in (("rocq", rocq), ("ocamlc", ocamlc)) if t is None]
  if missing:
    pytest.skip(f"{' and '.join(missing)} not installed; cannot build the "
                "extracted interpreters")
  assert rocq is not None and ocamlc is not None
  return rocq, ocamlc


def _run(cmd: list[str], what: str) -> None:
  """Run a build step, failing the test with its output if it does not work."""
  proc = subprocess.run(cmd, cwd=COQ, capture_output=True, text=True)
  if proc.returncode != 0:
    pytest.fail(f"{what} failed ({' '.join(cmd)}):\n"
                f"{proc.stdout[-2000:]}\n{proc.stderr[-2000:]}\n"
                "If this is a stale .vo from a different Rocq build, "
                "`cd coq && make clean && make` — see coq/README.md.")


def _build_driver(name: str, toolchain: tuple[str, str]) -> Path:
  rocq, ocamlc = toolchain
  source, module, driver_ml = _DRIVERS[name]
  binary = HARNESS / name
  if binary.exists():
    return binary
  if not (COQ / f"{module}.ml").exists():
    _run([rocq, "compile", source], f"extraction of {source}")
  _run([ocamlc, "-w", "-a", "-I", ".", "-I", "harness", "-o", f"harness/{name}",
        f"{module}.mli", f"{module}.ml", driver_ml], f"build of {name}")
  return binary


@pytest.fixture(scope="session")
def verified_driver(verified_toolchain) -> Path:
  """The array+procedure interpreter (`RevExtractAr`) — the most capable core."""
  return _build_driver("driverar", verified_toolchain)


@pytest.fixture(scope="session")
def core_driver(verified_toolchain) -> Path:
  """The plain core interpreter (`RevExtract`)."""
  return _build_driver("driver", verified_toolchain)


@pytest.fixture(scope="session")
def param_driver(verified_toolchain) -> Path:
  """The parameterized core (`RevExtractP`) — built by run.sh but never run."""
  return _build_driver("driverp", verified_toolchain)


@pytest.fixture(scope="session")
def vjanus_binary(verified_toolchain) -> Path:
  """The standalone verified interpreter, with its own OCaml jana2014 parser."""
  binary = COQ / "vjanus" / "vjanus"
  if not binary.exists():
    _run(["bash", "vjanus/build.sh"], "build of vjanus")
  return binary


@pytest.fixture(scope="session", autouse=True)
def _jana_py_importable() -> None:
  """The harnesses shell out to `python3 -m jana_py.cli`; let them find it."""
  os.environ["PYTHONPATH"] = str(ROOT) + os.pathsep + os.environ.get("PYTHONPATH", "")
