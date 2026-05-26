"""Smoke tests for the jana2014basic dialect (procedure-style, typeless params)."""
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

from jana_py.parser_jana2014basic import parse_program


def run_cli(source: str) -> subprocess.CompletedProcess[str]:
  env = dict(os.environ)
  env["PYTHONPATH"] = str(ROOT)
  with tempfile.NamedTemporaryFile("w", suffix=".ja", dir=ROOT, delete=False) as handle:
    handle.write(textwrap.dedent(source))
    path = handle.name
  try:
    return subprocess.run(
      [sys.executable, "-m", "jana_py.cli", "--std", "jana2014basic", "-s", path],
      cwd=ROOT, text=True, capture_output=True, env=env, check=False,
    )
  finally:
    Path(path).unlink(missing_ok=True)


class Jana2014BasicSmokeTests(unittest.TestCase):
  def test_procedure_main_with_typeless_params_parses(self) -> None:
    program = parse_program(
      "basic.ja",
      "procedure inc(x)\n    x += 1\n\nprocedure main()\n    int a\n    call inc(a)\n",
    )
    self.assertIsNotNone(program.main)
    self.assertEqual(program.procs[0].procname.name, "inc")

  def test_runs_via_cli(self) -> None:
    result = run_cli(
      """\
      procedure inc(x)
          x += 1

      procedure main()
          int a
          call inc(a)
      """
    )
    self.assertEqual(result.returncode, 0, result.stderr)
    self.assertEqual(result.stdout, "a = 1\n")

  def test_rejects_janus2026_void_main(self) -> None:
    with self.assertRaises(Exception):
      parse_program("bad.ja", "void main() { int x; x += 1; }")


if __name__ == "__main__":
  unittest.main()
