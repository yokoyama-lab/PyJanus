"""Smoke tests for the strict janus1982 dialect.

Distinctive traits: `procedure main` without parentheses, bare (typeless)
global variable declarations, and no procedure parameters.
"""
from __future__ import annotations

import os
from pathlib import Path
import subprocess
import sys
import tempfile
import textwrap
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from jana_py.parser_janus1982 import parse_program


def run_cli(source: str) -> subprocess.CompletedProcess[str]:
  env = dict(os.environ)
  env["PYTHONPATH"] = str(ROOT)
  with tempfile.NamedTemporaryFile("w", suffix=".ja", dir=ROOT, delete=False) as handle:
    handle.write(textwrap.dedent(source))
    path = handle.name
  try:
    return subprocess.run(
      [sys.executable, "-m", "jana_py.cli", "--std", "janus1982", "-s", path],
      cwd=ROOT, text=True, capture_output=True, env=env, check=False,
    )
  finally:
    Path(path).unlink(missing_ok=True)


class Janus1982SmokeTests(unittest.TestCase):
  def test_bare_global_and_paren_less_main_parse(self) -> None:
    program = parse_program("strict.ja", "x\nprocedure main\n    x += 1\n")
    self.assertIsNotNone(program.main)

  def test_runs_via_cli(self) -> None:
    result = run_cli("x\nprocedure main\n    x += 1\n")
    self.assertEqual(result.returncode, 0, result.stderr)
    self.assertEqual(result.stdout, "x = 1\n")

  def test_rejects_procedure_parameters(self) -> None:
    with self.assertRaises(Exception):
      parse_program("bad.ja", "procedure inc(x)\n    x += 1\n\nprocedure main\n    skip\n")


if __name__ == "__main__":
  unittest.main()
