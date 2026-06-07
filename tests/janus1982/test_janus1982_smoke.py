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


class InvertRoundTripTests(unittest.TestCase):
  """`-i` output must re-parse under the same strict dialect."""

  def _run(self, args: list[str], source: str | None = None, stdin: str | None = None):
    env = dict(os.environ)
    env["PYTHONPATH"] = str(ROOT)
    path = None
    if source is not None:
      with tempfile.NamedTemporaryFile("w", suffix=".ja", dir=ROOT, delete=False) as handle:
        handle.write(textwrap.dedent(source))
        path = handle.name
      args = [*args, path]
    try:
      return subprocess.run(
        [sys.executable, "-m", "jana_py.cli", "--std", "janus1982", *args],
        cwd=ROOT, text=True, capture_output=True, env=env, input=stdin, check=False,
      )
    finally:
      if path is not None:
        Path(path).unlink(missing_ok=True)

  def test_invert_emits_strict_1982_syntax(self) -> None:
    result = self._run(["-i"], "x\nprocedure main\n    x += 1\n    call double\n\nprocedure double\n    x += x\n")
    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
    self.assertIn("procedure main\n", result.stdout)   # no parens
    self.assertIn("call double\n", result.stdout)      # paren-less call
    self.assertNotIn("int x", result.stdout)            # globals are typeless
    self.assertTrue(result.stdout.startswith("x\n"), result.stdout)

  def test_invert_output_reparses(self) -> None:
    inverted = self._run(["-i"], "x\nprocedure main\n    x += 1\n    call double\n\nprocedure double\n    x += x\n")
    self.assertEqual(inverted.returncode, 0, inverted.stdout + inverted.stderr)
    reparse = self._run(["-a", "-"], stdin=inverted.stdout)
    self.assertEqual(reparse.returncode, 0, reparse.stdout + reparse.stderr)


if __name__ == "__main__":
  unittest.main()
