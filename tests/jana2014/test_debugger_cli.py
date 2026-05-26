from __future__ import annotations

import os
from pathlib import Path
import subprocess
import sys
import unittest


ROOT = Path(__file__).resolve().parents[1]
FROM_DEBUG_SIMPLE = "tests/fixtures/from_debug_simple.ja"
ITERATE_DEBUG_SIMPLE = "tests/fixtures/iterate_debug_simple.ja"


def run_python(args: list[str], stdin: str) -> subprocess.CompletedProcess[str]:
  env = dict(os.environ)
  env["PYTHONPATH"] = str(ROOT)
  return subprocess.run(
    [sys.executable, "-m", "jana_py.cli", *args],
    cwd=ROOT,
    text=True,
    input=stdin,
    capture_output=True,
    env=env,
    check=False,
  )


class DebuggerCliTests(unittest.TestCase):
  maxDiff = None

  def test_help_output_matches_eval_hs_text(self) -> None:
    result = run_python(["-d", "examples/fib.ja"], "h\nq\n")
    self.assertEqual(result.returncode, 0, result.stderr)
    self.assertIn('Welcome to the Jana debugger. Type "h[elp]" for the help menu.\n', result.stdout)
    self.assertIn("Usage of the jana debugger\n", result.stdout)
    self.assertIn(
      "IMPORTANT: all breakpoints will be added at the beginning of a line and only on statements.\n",
      result.stdout,
    )
    self.assertIn("options:\n", result.stdout)
    self.assertIn("  p[rint] V*   prints the content of variables V (space separated)\n", result.stdout)
    self.assertIn("  q[uit]       quit the debugger (ends termination)\n", result.stdout)

  def test_unknown_command_reports_expected_error_text(self) -> None:
    result = run_python(["-d", "examples/fib.ja"], "wat\nq\n")
    self.assertEqual(result.returncode, 0, result.stderr)
    self.assertIn('Unknown command: "wat". Type "h[elp]" to see known commands.\n', result.stdout)

  def test_next_stops_at_following_statement(self) -> None:
    result = run_python(["-d", "examples/fib.ja"], "n\nq\n")
    self.assertEqual(result.returncode, 0, result.stderr)
    self.assertEqual(
      result.stdout,
      'Welcome to the Jana debugger. Type "h[elp]" for the help menu.\n'
      '> [Break at line 20] \n'
      '> ',
    )

  def test_reverse_step_from_first_break_goes_to_begin(self) -> None:
    result = run_python(["-d", "examples/fib.ja"], "n\nr\nq\n")
    self.assertEqual(result.returncode, 0, result.stderr)
    self.assertEqual(
      result.stdout,
      'Welcome to the Jana debugger. Type "h[elp]" for the help menu.\n'
      '> [Break at line 20] \n'
      '> [Break at BEGIN (line 19)]\n'
      '> ',
    )

  def test_reverse_from_initial_prompt_terminates_with_store(self) -> None:
    result = run_python(["-d", "examples/fib.ja"], "r\n")
    self.assertEqual(result.returncode, 0, result.stderr)
    self.assertEqual(
      result.stdout,
      'Welcome to the Jana debugger. Type "h[elp]" for the help menu.\n'
      '> n = 0\n'
      'x1 = 0\n'
      'x2 = 0\n',
    )

  def test_backward_from_initial_prompt_terminates_with_store(self) -> None:
    result = run_python(["-d", "examples/fib.ja"], "b\n")
    self.assertEqual(result.returncode, 0, result.stderr)
    self.assertEqual(
      result.stdout,
      'Welcome to the Jana debugger. Type "h[elp]" for the help menu.\n'
      '> n = 0\n'
      'x1 = 0\n'
      'x2 = 0\n',
    )

  def test_stepping_enters_call_and_if_boundaries(self) -> None:
    result = run_python(["-d", "examples/fib.ja"], "n\nn\nn\nr\nr\nq\n")
    self.assertEqual(result.returncode, 0, result.stderr)
    self.assertEqual(
      result.stdout,
      'Welcome to the Jana debugger. Type "h[elp]" for the help menu.\n'
      '> [Break at line 20] \n'
      '> [Break at line 5] \n'
      '> [Break at line 9] \n'
      '> [Break at line 5] \n'
      '> [Break at line 20] \n'
      '> ',
    )

  def test_reverse_from_end_rewinds_to_last_visible_boundary(self) -> None:
    result = run_python(["-d", "examples/fib.ja"], "f\nr\nq\n")
    self.assertEqual(result.returncode, 0, result.stderr)
    self.assertEqual(
      result.stdout,
      'Welcome to the Jana debugger. Type "h[elp]" for the help menu.\n'
      '> [Break at END (_after_ line 22)]\n'
      '> [Break at line 5] \n'
      '> ',
    )

  def test_from_reverse_from_end_stops_at_inner_statement(self) -> None:
    result = run_python(["-d", FROM_DEBUG_SIMPLE], "f\nr\nq\n")
    self.assertEqual(result.returncode, 0, result.stderr)
    self.assertEqual(
      result.stdout,
      'Welcome to the Jana debugger. Type "h[elp]" for the help menu.\n'
      '> [Break at END (_after_ line 3)]\n'
      '> [Break at line 4] \n'
      '> ',
    )

  def test_from_reverse_after_completion_stops_at_inner_statement(self) -> None:
    result = run_python(["-d", FROM_DEBUG_SIMPLE], "n\nn\nr\nq\n")
    self.assertEqual(result.returncode, 0, result.stderr)
    self.assertEqual(
      result.stdout,
      'Welcome to the Jana debugger. Type "h[elp]" for the help menu.\n'
      '> [Break at line 4] \n'
      '> [Break at END (_after_ line 3)]\n'
      '> [Break at line 4] \n'
      '> ',
    )

  def test_iterate_next_treats_loop_as_single_statement(self) -> None:
    result = run_python(["-d", ITERATE_DEBUG_SIMPLE], "n\nq\n")
    self.assertEqual(result.returncode, 0, result.stderr)
    self.assertEqual(
      result.stdout,
      'Welcome to the Jana debugger. Type "h[elp]" for the help menu.\n'
      '> [Break at END (_after_ line 3)]\n'
      '> ',
    )

  def test_iterate_reverse_from_end_goes_to_begin(self) -> None:
    result = run_python(["-d", ITERATE_DEBUG_SIMPLE], "n\nr\nq\n")
    self.assertEqual(result.returncode, 0, result.stderr)
    self.assertEqual(
      result.stdout,
      'Welcome to the Jana debugger. Type "h[elp]" for the help menu.\n'
      '> [Break at END (_after_ line 3)]\n'
      '> [Break at BEGIN (line 3)]\n'
      '> ',
    )

  def test_iterate_forward_then_reverse_goes_to_begin(self) -> None:
    result = run_python(["-d", ITERATE_DEBUG_SIMPLE], "f\nr\nq\n")
    self.assertEqual(result.returncode, 0, result.stderr)
    self.assertEqual(
      result.stdout,
      'Welcome to the Jana debugger. Type "h[elp]" for the help menu.\n'
      '> [Break at END (_after_ line 3)]\n'
      '> [Break at BEGIN (line 3)]\n'
      '> ',
    )

  def test_call_reverse_stepping_crosses_procedure_boundary(self) -> None:
    result = run_python(["-d", "examples/fib.ja"], "f\nr\nr\nr\nq\n")
    self.assertEqual(result.returncode, 0, result.stderr)
    self.assertEqual(
      result.stdout,
      'Welcome to the Jana debugger. Type "h[elp]" for the help menu.\n'
      '> [Break at END (_after_ line 22)]\n'
      '> [Break at line 5] \n'
      '> [Break at line 9] \n'
      '> [Break at line 10] \n'
      '> ',
    )


if __name__ == "__main__":
  unittest.main()
