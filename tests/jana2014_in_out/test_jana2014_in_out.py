"""Tests for the jana2014_in_out dialect: reversible read/write + --direction/--expect."""
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

from jana_py.parser_jana2014_in_out import parse_program
from jana_py.ast import PrintsStmt

# A small reversible-I/O program: read two values, swap, write them back.
SWAP_IO = """\
procedure main()
    int x
    int y
    read x
    read y
    x <=> y
    write x
    write y
"""


def run_cli(source: str, *program_args: str, direction=None, expect=None,
            store=False) -> subprocess.CompletedProcess[str]:
  env = dict(os.environ)
  env["PYTHONPATH"] = str(ROOT)
  with tempfile.NamedTemporaryFile("w", suffix=".ja", dir=ROOT, delete=False) as handle:
    handle.write(textwrap.dedent(source))
    path = handle.name
  flags = ["--std", "jana2014_in_out"]
  if direction is not None:
    flags += ["--direction", direction]
  if expect is not None:
    flags += ["--expect", expect]
  if store:
    flags += ["-s"]
  try:
    return subprocess.run(
      [sys.executable, "-m", "jana_py.cli", *flags, path, *program_args],
      cwd=ROOT, text=True, capture_output=True, env=env, check=False,
    )
  finally:
    Path(path).unlink(missing_ok=True)


class ParseTests(unittest.TestCase):
  def test_read_write_parse_to_prints(self) -> None:
    prog = parse_program("io.ja", "procedure main()\n    int x\n    read x\n    write x\n")
    kinds = [s.prints.kind for s in prog.main.stmts if isinstance(s, PrintsStmt)]
    self.assertEqual(kinds, ["read", "write"])

  def test_inherits_jana2014_printf(self) -> None:
    # printf/show are still available (debug, non-consuming output).
    parse_program("io.ja", 'procedure main()\n    int x\n    read x\n    printf("%d", x)\n    write x\n')


class ForwardBackwardTests(unittest.TestCase):
  def test_forward_swaps_and_writes(self) -> None:
    result = run_cli(SWAP_IO, "3", "7", direction="forward")
    self.assertEqual(result.returncode, 0, result.stderr)
    self.assertEqual(result.stdout, "7\n3\n")
    self.assertEqual(result.stderr, "")  # write clears vars -> no leftover warning

  def test_backward_recovers_input(self) -> None:
    result = run_cli(SWAP_IO, "7", "3", direction="backward")
    self.assertEqual(result.returncode, 0, result.stderr)
    self.assertEqual(result.stdout, "3\n7\n")

  def test_roundtrip_forward_then_backward(self) -> None:
    fwd = run_cli(SWAP_IO, "3", "7", direction="forward", expect="7\n3")
    self.assertEqual(fwd.returncode, 0, fwd.stdout)
    self.assertIn("OK", fwd.stdout)
    bwd = run_cli(SWAP_IO, "7", "3", direction="backward", expect="3\n7")
    self.assertEqual(bwd.returncode, 0, bwd.stdout)
    self.assertIn("OK", bwd.stdout)


class ExpectTests(unittest.TestCase):
  def test_expect_match_exit_zero(self) -> None:
    result = run_cli(SWAP_IO, "3", "7", direction="forward", expect="7\n3")
    self.assertEqual(result.returncode, 0)
    self.assertIn("OK", result.stdout)

  def test_expect_mismatch_exit_one(self) -> None:
    result = run_cli(SWAP_IO, "3", "7", direction="forward", expect="wrong")
    self.assertEqual(result.returncode, 1)
    self.assertIn("MISMATCH", result.stdout)


class StrictReversibleIoTests(unittest.TestCase):
  def test_read_requires_zero_target(self) -> None:
    result = run_cli("procedure main()\n    int x = 5\n    read x\n    write x\n", "9")
    self.assertEqual(result.returncode, 1)
    self.assertIn("must be zero", result.stdout)

  def test_write_clears_variable(self) -> None:
    # After write, x is back to zero, so -s shows it as 0 and there is no warning.
    result = run_cli("procedure main()\n    int x\n    read x\n    write x\n", "42", store=True)
    self.assertEqual(result.returncode, 0, result.stderr)
    self.assertEqual(result.stdout, "42\nx = 0\n")
    self.assertEqual(result.stderr, "")


if __name__ == "__main__":
  unittest.main()
