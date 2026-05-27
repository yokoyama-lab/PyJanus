from __future__ import annotations

import os
from pathlib import Path
import subprocess
import sys
import unittest


ROOT = Path(__file__).resolve().parents[2]
EXAMPLE_DIR = ROOT / "tests" / "jana2014basic" / "fixtures" / "examples"


def run_ast(path: Path) -> subprocess.CompletedProcess[str]:
  env = dict(os.environ)
  env["PYTHONPATH"] = str(ROOT)
  return subprocess.run(
    [sys.executable, "-m", "jana_py.cli", "--std", "jana2014basic", "-a", str(path)],
    cwd=ROOT,
    text=True,
    capture_output=True,
    env=env,
    check=False,
  )


class BasicExampleFixtureTests(unittest.TestCase):
  def test_migrated_shared_examples_parse(self) -> None:
    for path in sorted(EXAMPLE_DIR.glob("*.ja")):
      with self.subTest(path=path.name):
        result = run_ast(path)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
  unittest.main()
