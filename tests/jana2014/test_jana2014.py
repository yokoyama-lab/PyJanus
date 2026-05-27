from __future__ import annotations

import os
from pathlib import Path
import subprocess
import sys
import textwrap

ROOT = Path(__file__).resolve().parents[2]


def run_python(args: list[str]) -> subprocess.CompletedProcess[str]:
  env = dict(os.environ)
  env["PYTHONPATH"] = str(ROOT / "src")
  return subprocess.run(
    [sys.executable, "-m", "jana_py.cli", *args],
    cwd=ROOT,
    text=True,
    capture_output=True,
    env=env,
    check=False,
  )


def test_jana2014_parameterized_procedure(tmp_path) -> None:
  path = tmp_path / "fib2014.ja"
  path.write_text(textwrap.dedent(
    """
    procedure fib(int x1, int x2, int n)
        if n = 0 then
            x1 += 1
            x2 += 1
        else
            n -= 1
            call fib(x1, x2, n)
            x1 += x2
            x1 <=> x2
        fi x1 = x2

    procedure main()
        int x1
        int x2
        int n
        n += 4
        call fib(x1, x2, n)
    """
  ))

  result = run_python(["--std", "jana2014", "-s", str(path)])
  assert result.returncode == 0, result.stderr
  assert "n = 0" in result.stdout
  assert "x1 = 5" in result.stdout
  assert "x2 = 8" in result.stdout


def test_jana2014basic_still_uses_basic_parser(tmp_path) -> None:
  path = tmp_path / "basic2014.ja"
  path.write_text(textwrap.dedent(
    """
    x
    procedure inc
        x += 1
    procedure main
        call inc
    """
  ))

  result = run_python(["--std", "jana2014basic", "-a", str(path)])
  assert result.returncode == 0, result.stderr
