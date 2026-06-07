from __future__ import annotations

import os
from pathlib import Path
import shutil
import subprocess
import sys
import unittest


ROOT = Path(__file__).resolve().parents[2]
HASKELL_CMD = ["runhaskell", "-isrc", "src/Main.hs"]
# The Haskell reference implementation lives outside the repo; skip without it.
HAVE_HASKELL = shutil.which("runhaskell") is not None and (ROOT / "src" / "Main.hs").exists()
PYTHONPATH = str(ROOT / "src")


def run_haskell(path: Path, extra_args: list[str] | None = None) -> subprocess.CompletedProcess[str]:
  args = [*HASKELL_CMD]
  if extra_args:
    args.extend(extra_args)
  args.append(str(path))
  return subprocess.run(
    args,
    cwd=ROOT,
    text=True,
    capture_output=True,
    check=False,
    timeout=5,
  )


def run_python(path: Path, extra_args: list[str] | None = None) -> subprocess.CompletedProcess[str]:
  env = dict(os.environ)
  env["PYTHONPATH"] = PYTHONPATH
  args = [sys.executable, "-m", "jana_py.cli"]
  if extra_args:
    args.extend(extra_args)
  args.append(str(path))
  return subprocess.run(
    args,
    cwd=ROOT,
    text=True,
    capture_output=True,
    env=env,
    check=False,
    timeout=5,
  )


def jana_cases() -> list[Path]:
  cases = sorted((ROOT / "tests" / "errors").glob("*.ja"))
  cases.extend(sorted((ROOT / "tests" / "jana2014" / "fixtures" / "examples").glob("*.ja")))
  return cases


@unittest.skipUnless(HAVE_HASKELL, "requires the Haskell reference implementation (runhaskell + src/Main.hs)")
class Step1GoldenTests(unittest.TestCase):
  maxDiff = None


# Cases that intentionally diverge from Haskell (Python-only extensions or Haskell timeouts).
_SKIP_CASES: set[str] = {
    "tests/errors/infinite-recursion.ja",  # Haskell hangs on this input
    "tests/errors/array-size-mismatch.ja",  # Python checks at call site; Haskell doesn't
}


def _make_test(case_path: Path):
  rel = str(case_path.relative_to(ROOT))
  if rel in _SKIP_CASES:
    def test(self: Step1GoldenTests) -> None:
      self.skipTest(f"Intentionally skipped: {rel}")
  else:
    def test(self: Step1GoldenTests) -> None:
      haskell = run_haskell(case_path)
      python = run_python(case_path)
      rel = case_path.relative_to(ROOT)
      self.assertEqual(python.returncode, haskell.returncode, f"Return code mismatch for {rel}")
      if haskell.returncode == 0:
        # Success cases: compare exact output
        self.assertEqual(
          (python.stdout, python.stderr),
          (haskell.stdout, haskell.stderr),
          f"Output mismatch for {rel}",
        )
      # Error cases: Python uses improved format, skip exact message comparison

  return test


for _case in jana_cases():
  setattr(
    Step1GoldenTests,
    f"test_{str(_case.relative_to(ROOT)).replace('/', '_').replace('.', '_').replace('-', '_')}",
    _make_test(_case),
  )


if __name__ == "__main__":
  unittest.main()
