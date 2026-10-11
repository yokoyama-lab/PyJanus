"""Tests for tally_differential.py: known tiny inputs give the expected counts,
and adding one test case moves exactly one count by one."""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import tally_differential as T  # noqa: E402

JUNIT = """<?xml version="1.0"?><testsuites><testsuite>
<testcase classname="tests.jana2014.test_verified_corpus" name="test_verified_matches_pyjanus[a.ja]"/>
<testcase classname="tests.jana2014.test_verified_corpus" name="test_verified_matches_pyjanus[b.ja]"><skipped message="*="/></testcase>
<testcase classname="tests.jana2014.test_vjanus_corpus" name="t[a.ja]"/>
<testcase classname="tests.jana2014.test_vjanus_inverse" name="t[a.ja]"><failure message="x"/></testcase>
{extra}
</testsuite></testsuites>"""

CODEGEN = "PASS   a.ja\nWARNING noise\nWRONG  b.ja: out[0]: cpp=1 interp=2\n\nPASS=1, WRONG=1\n"


def _junit(tmp: Path, extra: str = "") -> Path:
  p = tmp / "j.xml"
  p.write_text(JUNIT.format(extra=extra))
  return p


def test_known_counts(tmp_path):
  rows = T.tally_junit(_junit(tmp_path))
  assert rows[("test_verified_corpus", "passed")] == 1
  assert rows[("test_verified_corpus", "skipped")] == 1
  assert rows[("test_vjanus_corpus", "passed")] == 1
  assert rows[("test_vjanus_inverse", "failed")] == 1
  assert T.skip_reasons(_junit(tmp_path), "test_verified_corpus") == {"*=": ["b.ja"]}


def test_adding_one_case_adds_one(tmp_path):
  before = T.tally_junit(_junit(tmp_path))
  extra = ('<testcase classname="tests.jana2014.test_verified_corpus" '
           'name="test_verified_matches_pyjanus[c.ja]"/>')
  after = T.tally_junit(_junit(tmp_path, extra))
  assert after[("test_verified_corpus", "passed")] == before[("test_verified_corpus", "passed")] + 1
  assert sum(after.values()) == sum(before.values()) + 1


def test_codegen_log(tmp_path):
  p = tmp_path / "c.log"
  p.write_text(CODEGEN)
  tags, nonpass = T.tally_codegen(p)
  assert tags == {"PASS": 1, "WRONG": 1}
  assert nonpass == [("WRONG", "b.ja")]
  p.write_text(CODEGEN.replace("\n\n", "\nPASS   c.ja\n\n").replace("PASS=1", "PASS=2"))
  assert T.tally_codegen(p)[0]["PASS"] == 2


def test_summary_line_mismatch_is_detected(tmp_path):
  p = tmp_path / "c.log"
  p.write_text(CODEGEN.replace("PASS=1, WRONG=1", "PASS=5, WRONG=1"))
  try:
    T.tally_codegen(p)
  except ValueError:
    return
  raise AssertionError("summary mismatch not detected")
