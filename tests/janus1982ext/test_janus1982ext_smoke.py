"""Smoke tests for the janus1982ext dialect (1982 + extensions).

Distinctive traits: `procedure main` without parentheses, but unlike strict
janus1982 it supports procedure parameters (typed or typeless) and local
declarations with initializers.
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

from jana_py.parser_janus1982ext import parse_program


def run_cli(source: str) -> subprocess.CompletedProcess[str]:
  env = dict(os.environ)
  env["PYTHONPATH"] = str(ROOT)
  with tempfile.NamedTemporaryFile("w", suffix=".ja", dir=ROOT, delete=False) as handle:
    handle.write(textwrap.dedent(source))
    path = handle.name
  try:
    return subprocess.run(
      [sys.executable, "-m", "jana_py.cli", "--std", "janus1982ext", "-s", path],
      cwd=ROOT, text=True, capture_output=True, env=env, check=False,
    )
  finally:
    Path(path).unlink(missing_ok=True)


class Janus1982ExtSmokeTests(unittest.TestCase):
  def test_paren_less_main_with_typed_local_parses(self) -> None:
    program = parse_program("ext.ja", "procedure main\n    int x\n    x += 1\n")
    self.assertIsNotNone(program.main)

  def test_supports_procedure_parameters(self) -> None:
    program = parse_program(
      "ext.ja",
      "procedure inc(int x)\n    x += 1\n\nprocedure main\n    int a\n    call inc(a)\n",
    )
    self.assertEqual(program.procs[0].procname.name, "inc")

  def test_runs_via_cli(self) -> None:
    result = run_cli(
      "procedure inc(int x)\n    x += 1\n\nprocedure main\n    int a\n    call inc(a)\n"
    )
    self.assertEqual(result.returncode, 0, result.stderr)
    self.assertEqual(result.stdout, "a = 1\n")


if __name__ == "__main__":
  unittest.main()
