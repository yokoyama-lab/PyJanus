"""生成 AI による自動修復向けヒント（PYJANUS_REPAIR_HINTS=1）の検査（2026-11-04）。"""
from __future__ import annotations

import os
from pathlib import Path
import subprocess
import sys
import tempfile
import textwrap
import unittest

from jana_py.errors import _repair_hints

ROOT = Path(__file__).resolve().parents[1]


def run_source(source: str, hints: bool) -> str:
  with tempfile.NamedTemporaryFile("w", suffix=".ja", dir=ROOT, delete=False) as handle:
    handle.write(textwrap.dedent(source))
    path = handle.name
  env = dict(os.environ, PYTHONPATH=str(ROOT))
  env.pop("PYJANUS_REPAIR_HINTS", None)
  if hints:
    env["PYJANUS_REPAIR_HINTS"] = "1"
  try:
    r = subprocess.run([sys.executable, "-m", "jana_py.cli", "--std", "jana2014_in_out", path],
                       cwd=ROOT, text=True, capture_output=True, env=env, check=False)
    return r.stdout + r.stderr
  finally:
    Path(path).unlink(missing_ok=True)


ASSIGN = """\
procedure main()
    int x
    int t
    x = t
"""


class RepairHintRuleTests(unittest.TestCase):
  def hints(self, line: str, msg: str = "Expecting statement") -> str:
    return "\n".join(_repair_hints(msg, line, "jana2014_in_out"))

  def test_plain_assignment(self) -> None:
    self.assertIn("no assignment `=`", self.hints("    z = t"))
    self.assertIn("`z += e`", self.hints("    z = t"))

  def test_colon_assignment_and_le(self) -> None:
    self.assertIn("no assignment `:=`", self.hints("x := y"))
    self.assertIn("no assignment `<=`", self.hints("x <= y"))

  def test_array_element_assignment(self) -> None:
    self.assertIn("`a[i] += e`", self.hints("a[i] = 3"))

  def test_comparison_is_not_assignment(self) -> None:
    for line in ["if x = 0 then", "from i = 0 do", "local int t = x", "delocal int t = x",
                 "x += 1", "x <=> y"]:
      self.assertNotIn("no assignment", self.hints(line), line)

  def test_swap_with_constant(self) -> None:
    self.assertIn("constant cannot be swapped", self.hints("x <=> 0", "Expecting identifier"))

  def test_call_without_keyword(self) -> None:
    self.assertIn("`call swap(...)`", self.hints("swap(x, y)"))
    self.assertNotIn("call if", self.hints("if (x = 0) then"))

  def test_local_list_needs_types(self) -> None:
    self.assertIn("needs its own type", self.hints("local int a = 0, b = 1"))

  def test_other_languages(self) -> None:
    self.assertIn("from <entry condition>", self.hints("while x > 0"))
    self.assertIn("no `return`", self.hints("return x"))
    self.assertIn("no `else if`", self.hints("else if x = 1 then"))
    self.assertIn("no braces", self.hints("x += 1;"))

  def test_braces_allowed_in_janus2026(self) -> None:
    self.assertEqual(_repair_hints("Expecting statement", "x += 1;", "janus2026"),
                     _repair_hints("Expecting statement", "", "janus2026"))

  def test_generic_fallback(self) -> None:
    self.assertIn("A statement must be one of", self.hints("???"))


class RepairHintCliTests(unittest.TestCase):
  def test_off_by_default(self) -> None:
    out = run_source(ASSIGN, hints=False)
    self.assertIn("PyJanus parsing error", out)
    self.assertNotIn("no assignment", out)

  def test_on_with_env(self) -> None:
    out = run_source(ASSIGN, hints=True)
    self.assertIn("Fix hints:", out)
    self.assertIn("Janus has no assignment `=`", out)


if __name__ == "__main__":
  unittest.main()
