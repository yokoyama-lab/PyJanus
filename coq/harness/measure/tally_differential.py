#!/usr/bin/env python3
"""Count the differential-testing results that the Janus mechanization paper
quotes, from the raw outputs of one re-measurement run.

Inputs (written by remeasure.sh):
  junit.xml          pytest --junitxml over the four differential suites
  codegen_diff.log   coq/harness/codegen_diff.py over the whole corpus

Output: a TSV of (quantity, value) on stdout.  Nothing here is typed by hand;
every number is a count over the raw files.  Exit 1 if the codegen log's own
summary line disagrees with the per-file lines (a truncated log).
"""
from __future__ import annotations

import collections
import re
import sys
import xml.etree.ElementTree as ET
from pathlib import Path


def _status(tc: ET.Element) -> str:
  for ch in tc:
    if ch.tag == "skipped":
      return "skipped"
    if ch.tag in ("failure", "error"):
      return "failed"
  return "passed"


def _param(name: str) -> str:
  m = re.search(r"\[(.*)\]$", name)
  return m.group(1) if m else name


def tally_junit(path: Path) -> collections.Counter:
  """(suite, status) -> count."""
  c: collections.Counter = collections.Counter()
  for tc in ET.parse(path).iter("testcase"):
    c[(tc.get("classname", "").split(".")[-1], _status(tc))] += 1
  return c


def skip_reasons(path: Path, suite: str) -> dict[str, list[str]]:
  out: dict[str, list[str]] = collections.defaultdict(list)
  for tc in ET.parse(path).iter("testcase"):
    if tc.get("classname", "").split(".")[-1] != suite or _status(tc) != "skipped":
      continue
    sk = next(ch for ch in tc if ch.tag == "skipped")
    out[sk.get("message", "")].append(_param(tc.get("name", "")))
  return dict(out)


TAGS = ("PASS", "WRONG", "CFAIL", "CGERR", "SKIP", "ERROR")


def tally_codegen(path: Path) -> tuple[dict[str, int], list[tuple[str, str]]]:
  tags: collections.Counter = collections.Counter()
  nonpass: list[tuple[str, str]] = []
  summary = None
  for line in path.read_text().splitlines():
    m = re.match(r"^(%s)\s+(\S+?):?(\s|$)" % "|".join(TAGS), line)
    if m and "=" not in m.group(2):
      tags[m.group(1)] += 1
      if m.group(1) != "PASS":
        nonpass.append((m.group(1), m.group(2)))
    elif re.match(r"^(%s)=\d+" % "|".join(TAGS), line):
      summary = {k: int(v) for k, v in re.findall(r"(\w+)=(\d+)", line)}
  if summary is not None and summary != dict(tags):
    raise ValueError(f"summary {summary} != per-file {dict(tags)} (truncated log?)")
  return dict(tags), nonpass


def main(argv: list[str]) -> int:
  run = Path(argv[1])
  j = tally_junit(run / "junit.xml")
  print("quantity\tvalue")
  for (suite, st), n in sorted(j.items()):
    print(f"junit.{suite}.{st}\t{n}")
  for reason, progs in sorted(skip_reasons(run / "junit.xml", "test_verified_corpus").items()):
    print(f"skip.test_verified_corpus[{reason}]\t{len(progs)}\t{' '.join(sorted(progs))}")
  try:
    tags, nonpass = tally_codegen(run / "codegen_diff.log")
  except ValueError as e:
    print(f"ERROR\t{e}", file=sys.stderr)
    return 1
  for t, n in sorted(tags.items()):
    print(f"codegen_diff.{t}\t{n}")
  for t, prog in nonpass:
    print(f"codegen_diff.nonpass\t{t}\t{prog}")
  return 0


if __name__ == "__main__":
  sys.exit(main(sys.argv))
