"""Each error fixture must produce the diagnostic it was written to produce.

`fixtures_errors/*.ja` are programs the interpreter has to reject. Checking only
that they exit non-zero is much weaker than it looks: a fixture written to
provoke an aliasing error keeps passing if the interpreter starts reporting a
parse error instead, or the right error in the wrong phase, or a different error
entirely. Six of the fifty-two had their message asserted by hand in
`test_m2.py`; the rest were only checked for failure.

The header each fixture now carries names the diagnostic, and this compares it
against the run. The source *location* is deliberately not pinned -- it is a
line number, and these files gain comment lines -- so this is about what the
interpreter says, not where.
"""

from __future__ import annotations

import glob
import sys
import unittest
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))

from check_error_fixtures import KINDS, check_file, diagnose, read_header  # noqa: E402

FIXTURES = sorted(glob.glob(str(ROOT / "tests" / "jana2014" / "fixtures_errors" / "*.ja")))


@pytest.mark.parametrize("ja", FIXTURES, ids=lambda p: Path(p).name)
def test_reports_the_diagnostic_it_declares(ja: str) -> None:
  path = Path(ja)
  if not read_header(path):
    pytest.skip("no diagnostic header yet")
  problems = check_file(path)
  assert not problems, f"{path.name}:\n  " + "\n  ".join(problems)


@pytest.mark.parametrize("ja", FIXTURES, ids=lambda p: Path(p).name)
def test_is_rejected_at_all(ja: str) -> None:
  # True of every fixture, header or no header: this is the property the
  # directory exists for.
  status, _, _ = diagnose(Path(ja))
  assert status != 0, f"{Path(ja).name} succeeded, but it is an error fixture"


class ErrorFixtureHeaderTests(unittest.TestCase):
  def test_every_fixture_names_its_diagnostic(self) -> None:
    missing = [Path(ja).name for ja in FIXTURES if not read_header(Path(ja))]
    self.assertEqual(missing, [], "error fixtures with no diagnostic header")

  def test_kinds_are_from_the_vocabulary(self) -> None:
    for ja in FIXTURES:
      kind = read_header(Path(ja)).get("error-kind")
      self.assertIn(kind, KINDS, f"{Path(ja).name}: {kind}")

  def test_only_one_fixture_escapes_the_diagnostic_machinery(self) -> None:
    # `uncaught` means PyJanus never printed a diagnostic at all -- something
    # else ended the run. Exactly one fixture does that today
    # (infinite-recursion, which surfaces a Python RecursionError), and pinning
    # the count here means a second one cannot appear unnoticed.
    uncaught = sorted(Path(ja).stem for ja in FIXTURES
                      if read_header(Path(ja)).get("error-kind") == "uncaught")
    self.assertEqual(uncaught, ["infinite-recursion"])


if __name__ == "__main__":
  unittest.main()
