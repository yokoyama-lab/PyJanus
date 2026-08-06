#!/usr/bin/env python3
"""Pin what each error fixture is supposed to say, not merely that it fails.

`tests/jana2014/fixtures_errors/*.ja` are programs that must be rejected. Until
now almost all of them were checked only for a non-zero exit: a handful have
their message asserted in `tests/jana2014/test_m2.py`, and the rest would go on
passing if the interpreter started reporting an unrelated error, or a much worse
one, or the same one in a different category.

So each fixture carries a header naming the diagnostic it is there to provoke:

    // @summary:    two formals bound to the same variable
    // @error-kind: execution
    // @error:      Identifiers `a' and `b' are aliases

`@error-kind` is the category PyJanus prints on its first line -- `parsing`
happens before anything runs, `validation` before execution starts, `execution`
during -- and moving a diagnostic between them is a real behaviour change that
this pins. `@error` is the `message:` line verbatim.

Deliberately *not* pinned: the source location. It is a line number, and these
files acquire comment lines; a golden keyed to it would break every time
somebody edited a header, which is exactly the tripwire that had to be removed
from the debugger tests. Locations are covered by `tests/test_error_reporting.py`.

Usage:

    tools/check_error_fixtures.py report        # coverage, and the kinds in use
    tools/check_error_fixtures.py check         # verify every annotated fixture
    tools/check_error_fixtures.py stub a.ja     # print a header to paste in
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from check_corpus_meta import FIELD_RE, normalized_text  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / "tests" / "jana2014" / "fixtures_errors"
STD = "jana2014"

ORDER = ("summary", "error-kind", "error")

#: The categories PyJanus prints. `uncaught` is not one of its own: it is what
#: this tool records when a fixture escapes the diagnostic machinery entirely
#: and something else -- a Python exception, say -- ends the run instead.
KINDS = ("parsing", "validation", "execution", "uncaught")

HEAD_RE = re.compile(r"^PyJanus (\w+) error$")
MESSAGE_RE = re.compile(r"^  message: (.*)$")


def diagnose(path: Path, timeout: float = 60.0) -> tuple[int, str, str]:
  """Run the fixture and return (exit status, error kind, message)."""
  result = subprocess.run(
    [sys.executable, "-m", "jana_py.cli", "--std", STD, str(path)],
    cwd=ROOT, capture_output=True, text=True, timeout=timeout)
  lines = result.stdout.splitlines()
  for index, line in enumerate(lines):
    head = HEAD_RE.match(line)
    if head:
      for follower in lines[index + 1:]:
        message = MESSAGE_RE.match(follower)
        if message:
          return result.returncode, head.group(1), message.group(1)
      return result.returncode, head.group(1), ""
  # No PyJanus diagnostic at all: record whatever did come out, so that the
  # fixture still says something definite about what happens to it.
  fallback = (lines or result.stderr.splitlines() or [""])[0]
  return result.returncode, "uncaught", fallback


def read_header(path: Path) -> dict[str, str]:
  fields = {}
  for line in path.read_text().splitlines():
    match = FIELD_RE.match(line)
    if match:
      fields[match.group(1)] = match.group(2).strip()
  return fields


def check_file(path: Path) -> list[str]:
  header = read_header(path)
  if not header:
    return []

  problems = [f"missing `@{name}:`" for name in ORDER if name not in header]
  unknown = [name for name in header if name not in ORDER]
  problems += [f"unknown field `@{name}:` (known: {', '.join(ORDER)})" for name in unknown]
  if header.get("error-kind") and header["error-kind"] not in KINDS:
    problems.append(f"`@error-kind: {header['error-kind']}` is not one of {', '.join(KINDS)}")
  if problems:
    return problems

  status, kind, message = diagnose(path)
  if status == 0:
    problems.append("the program succeeded; an error fixture must be rejected")
  if kind != header["error-kind"]:
    problems.append(f"`@error-kind:` says {header['error-kind']}, but the run reported {kind}")
  if message != header["error"]:
    problems.append(f"`@error:` says {header['error']!r}, but the run reported {message!r}")
  return problems


def targets(paths: list[str]) -> list[Path]:
  return [Path(p).resolve() for p in paths] if paths else sorted(FIXTURES.glob("*.ja"))


def cmd_report(args: argparse.Namespace) -> int:
  files = targets(args.files)
  annotated = [p for p in files if read_header(p)]
  print(f"annotated {len(annotated)}/{len(files)}")

  tally: dict[str, int] = {}
  for path in annotated:
    kind = read_header(path).get("error-kind", "(none)")
    tally[kind] = tally.get(kind, 0) + 1
  if tally:
    print("\nby kind:")
    for kind, count in sorted(tally.items(), key=lambda kv: -kv[1]):
      print(f"  {count:3d}  {kind}")

  missing = [p for p in files if p not in annotated]
  if missing and not args.quiet:
    print("\nnot yet annotated:")
    for path in missing:
      print(f"  {path.name}")
  return 0


def cmd_check(args: argparse.Namespace) -> int:
  checked = failed = 0
  for path in targets(args.files):
    if not read_header(path):
      continue
    checked += 1
    problems = check_file(path)
    if problems:
      failed += 1
      print(f"FAIL {path.name}")
      for problem in problems:
        print(f"     {problem}")
  print(f"\nchecked {checked} annotated fixture(s), {failed} failed")
  return 1 if failed else 0


def cmd_stub(args: argparse.Namespace) -> int:
  for path in targets(args.files):
    _, kind, message = diagnose(path)
    print(f"// ---- paste at the top of {path.name} ----")
    print("// @summary:    TODO one line: what mistake does this program make?")
    print(f"// @error-kind: {kind}")
    print(f"// @error:      {message}")
  return 0


def main() -> int:
  parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
  sub = parser.add_subparsers(dest="command", required=True)
  for name, handler, help_text in (
    ("report", cmd_report, "show how many fixtures name their diagnostic"),
    ("check", cmd_check, "verify the headers against what the fixtures actually report"),
    ("stub", cmd_stub, "print a header for a fixture, with the diagnostic filled in"),
  ):
    child = sub.add_parser(name, help=help_text)
    child.add_argument("files", nargs="*", help="default: every error fixture")
    child.add_argument("-q", "--quiet", action="store_true", help="report: omit the unannotated list")
    child.set_defaults(handler=handler)
  args = parser.parse_args()
  return args.handler(args)


if __name__ == "__main__":
  sys.exit(main())
