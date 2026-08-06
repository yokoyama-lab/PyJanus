#!/usr/bin/env python3
"""Check the structured metadata headers of the example corpus.

`tests/jana2014/fixtures/examples/*.ja` is checked by eight glob-based corpus
tests, but every one of them checks a *self-consistency* property: that running
the program and then its inverse restores the store, that the C++ back-end
agrees with the interpreter, that the formatter round-trips, that the two
verified cores agree.  None of them says what a program is supposed to
*compute*.  A program that computes the wrong thing, reversibly, passes them
all.

This tool checks a metadata header that pins that missing information:

    // @summary:   recursive Fibonacci: leaves the pair (F(n+1), F(n+2)) in (x1, x2)
    // @technique: clean-accumulation
    // @source:    Yokoyama & Gluck, PEPM 2007, Fig. 1
    // @confirmed: F(1)=F(2)=1 gives 1,1,2,3,5,8,13, so n=5 yields (8,13)
    // @keep:      n
    // @oracle:    n == 5 and x1 == 0 and x2 == 0
    // @expect: 0 8 13
    // @expect: n = 5
    // @expect: x1 = 0
    // @expect: x2 = 0

The two machine-checked fields answer two different questions:

`@expect` is the verbatim standard output of

    python3 -m jana_py.cli --std jana2014 -s <file>

one comment line per output line, in order.  It is a golden pin: it says *what
the program does today* and fails when that changes for any reason.  Writing it
requires no understanding -- `stub` fills it in.

`@oracle` is a Python expression over the final store, and it says *what the
program is supposed to compute*.  It is written independently of the program's
output -- from the definition of the algorithm, a textbook value, or a Python
one-liner -- so it can disagree with the program, which is the entire point.
It is optional, because for some programs the honest answer is that nobody has
worked out the right value yet; those carry `@confirmed: UNVERIFIED -- ...`
instead and `report` lists them.

`@confirmed` is the part no machine can check: how a human established that the
pinned values are the right ones.

`@keep` names the variables the run is *supposed* to leave non-zero: the inputs
the program preserves, plus the answer.  Everything else still holding a value
is **garbage** -- the history a reversible program must retain to stay
injective (a quotient stack, a decision log, a sorting permutation).  Which of
the survivors is the answer cannot be read off a run, so that one line is
declared and the rest is derived.  A program with garbage is named `..._g.ja` and
one without is named `..._c.ja`; the check is total, so an unclassified name and
a `_g` name with no garbage both fail.

Annotating is incremental.  A file with no `@` fields at all is reported as
unannotated, not as a failure, so the corpus can be annotated a few files at a
time without ever breaking CI.  A file with *some* of the fields is an error,
because a half-written header is a mistake rather than a stage.

Usage:

    tools/check_corpus_meta.py report          # how far along the corpus is
    tools/check_corpus_meta.py check           # verify every annotated file
    tools/check_corpus_meta.py check a.ja      # verify just this one
    tools/check_corpus_meta.py stub a.ja       # print a header to paste in
    tools/check_corpus_meta.py store a.ja      # print the store @oracle sees
    tools/check_corpus_meta.py normalize       # rewrite headers into house style
"""

from __future__ import annotations

import argparse
import builtins
import math
import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
EXAMPLES = ROOT / "tests" / "jana2014" / "fixtures" / "examples"
STD = "jana2014"

#: Field order is part of the house style, and `check` enforces it.  `oracle` is
#: the only optional field; `expect` is the only repeatable one, and comes last.
ORDER = ("summary", "technique", "source", "confirmed", "keep", "oracle", "expect")
REQUIRED = ("summary", "technique", "source", "confirmed", "keep", "expect")
REPEATABLE = ("expect",)

#: `@keep: none` means the final store is expected to be entirely trivial.
KEEP_NONE = "none"

#: Every example says in its name whether it leaves garbage.  See `garbage_of`.
GARBAGE_SUFFIX = "_g"
CLEAN_SUFFIX = "_c"

#: The four ways to make an irreversible computation reversible, from
#: `docs/textbook-programs-plan.md` §3, plus `plain` for programs that are
#: already injective and need no trick.
TECHNIQUES = (
  "clean-accumulation",
  "ancilla-flag",
  "history-stack",
  "bennett-uncompute",
  "plain",
)

#: Lowercase, digits and underscores.  Hyphens and dots are out: `.ja` names are
#: used as pytest ids and as C++ identifiers by the codegen differential test.
FILENAME_RE = re.compile(r"^[a-z][a-z0-9_]*\.ja$")

FIELD_RE = re.compile(r"^\s*//\s*@([A-Za-z][A-Za-z0-9-]*)\s*: ?(.*?)[ \t]*$")


# ---------------------------------------------------------------------------
# the store, as `@oracle` sees it
# ---------------------------------------------------------------------------


class Struct(dict):
  """A Janus struct in the oracle namespace, reachable as `p.x` or `p["x"]`."""

  def __getattr__(self, name: str) -> Any:
    try:
      return self[name]
    except KeyError:
      raise AttributeError(name) from None


#: `pyjanus -s` prints one line per variable in a small, regular grammar:
#:
#:     line  := name index* " = " value
#:     value := int | "nil" | "<" items "]" | "{" items "}" | "{" field,+ "}"
#:
#: `nil` and `<..]` are stacks (leftmost is the top), `{..}` without `=` is an
#: array, `{..}` with `=` is a struct.  Arrays and structs nest.
STORE_LINE_RE = re.compile(r"^([A-Za-z_][A-Za-z0-9_]*)((?:\[[0-9]+\])*) = (.*)$")


def _split_items(text: str) -> list[str]:
  """Split `a, b, c` at top-level commas, respecting `{}` and `<]` nesting."""
  items, depth, current = [], 0, ""
  for char in text:
    if char in "{<":
      depth += 1
    elif char in "}]":
      depth -= 1
    if char == "," and depth == 0:
      items.append(current)
      current = ""
    else:
      current += char
  if current.strip():
    items.append(current)
  return [item.strip() for item in items]


def parse_value(text: str) -> Any:
  text = text.strip()
  if text == "nil":
    return []
  if text.startswith("<") and text.endswith("]"):
    return [parse_value(item) for item in _split_items(text[1:-1])]
  if text.startswith("{") and text.endswith("}"):
    items = _split_items(text[1:-1])
    if items and all(re.match(r"^[A-Za-z_][A-Za-z0-9_]* = ", item) for item in items):
      struct = Struct()
      for item in items:
        name, _, value = item.partition(" = ")
        struct[name] = parse_value(value)
      return struct
    return [parse_value(item) for item in items]
  return int(text)


def parse_store(lines: list[str]) -> dict[str, Any]:
  """Turn the store half of `-s` output into a namespace for `@oracle`."""
  store: dict[str, Any] = {}
  for line in lines:
    match = STORE_LINE_RE.match(line)
    if match is None:
      raise ValueError(f"cannot parse store line {line!r}")
    store[match.group(1)] = parse_value(match.group(3))
  return store


#: What an `@oracle` expression may call.  Deliberately small: the oracle should
#: read as a statement of the expected answer, not as a second implementation.
ORACLE_BUILTINS = {
  name: getattr(builtins, name)
  for name in (
    "abs", "all", "any", "divmod", "enumerate", "int", "len", "list",
    "max", "min", "pow", "range", "reversed", "set", "sorted", "sum", "tuple", "zip",
  )
}
ORACLE_BUILTINS.update({
  "comb": math.comb,
  "factorial": math.factorial,
  "gcd": math.gcd,
  "isqrt": math.isqrt,
  "lcm": math.lcm,
})


def evaluate_oracle(expression: str, store: dict[str, Any]) -> tuple[bool, str]:
  """Evaluate an `@oracle` expression against the store. Returns (ok, detail)."""
  namespace: dict[str, Any] = {"__builtins__": ORACLE_BUILTINS}
  namespace.update(store)
  try:
    value = eval(expression, namespace)  # noqa: S307 -- repo-controlled fixtures
  except Exception as exc:  # noqa: BLE001 -- any failure is a reportable problem
    return False, f"{type(exc).__name__}: {exc}"
  if not isinstance(value, bool):
    return False, f"evaluated to {value!r}, which is not True or False"
  return value, "" if value else f"is false for the final store: {_render(store)}"


def _render(store: dict[str, Any]) -> str:
  return ", ".join(f"{name}={value}" for name, value in store.items())


# ---------------------------------------------------------------------------
# garbage
# ---------------------------------------------------------------------------


def is_trivial(value: Any) -> bool:
  """True when a store value is all zeros -- an empty stack, a zeroed array."""
  if isinstance(value, int):
    return value == 0
  if isinstance(value, dict):
    return all(is_trivial(field_value) for field_value in value.values())
  return all(is_trivial(item) for item in value)


def parse_keep(value: str) -> list[str]:
  if value.strip() == KEEP_NONE:
    return []
  return [name.strip() for name in value.split(",") if name.strip()]


def garbage_of(store: dict[str, Any], keep: list[str]) -> list[str]:
  """The variables left holding information that is neither input nor answer.

  Which of the surviving values *is* the answer cannot be read off a run: the
  program ends, and every non-zero variable looks alike.  So one thing is
  declared -- `@keep`, the inputs the program preserves plus the result it
  produces -- and garbage is everything else the run left behind.  A reversible
  program that must record history to stay injective (a quotient stack, a
  decision log, a sorting permutation) shows up here, and that is what the
  `_g` filename suffix marks.
  """
  return sorted(name for name, value in store.items() if not is_trivial(value) and name not in keep)


# ---------------------------------------------------------------------------
# the header
# ---------------------------------------------------------------------------


@dataclass
class Meta:
  """The `@` fields of one file, plus whatever was wrong with them."""

  path: Path
  fields: dict[str, list[str]] = field(default_factory=dict)
  lines: dict[str, int] = field(default_factory=dict)
  errors: list[str] = field(default_factory=list)

  @property
  def annotated(self) -> bool:
    return bool(self.fields)

  def one(self, name: str) -> str:
    return (self.fields.get(name) or [""])[0]


def parse_meta(path: Path) -> Meta:
  """Read the `// @field: value` lines out of `path` and validate their shape."""
  meta = Meta(path=path)
  seen: list[tuple[int, str]] = []

  for lineno, line in enumerate(path.read_text().splitlines(), start=1):
    match = FIELD_RE.match(line)
    if match is None:
      continue
    name, value = match.group(1), match.group(2)
    if name not in REPEATABLE:
      value = value.strip()
    if name not in ORDER:
      meta.errors.append(f"line {lineno}: unknown field `@{name}:` (known: {', '.join(ORDER)})")
      continue
    if name in meta.fields and name not in REPEATABLE:
      meta.errors.append(f"line {lineno}: `@{name}:` given twice (only @expect may repeat)")
      continue
    meta.fields.setdefault(name, []).append(value)
    meta.lines.setdefault(name, lineno)
    seen.append((lineno, name))

  if not meta.annotated:
    return meta

  for name in REQUIRED:
    if name not in meta.fields:
      meta.errors.append(f"missing `@{name}:`")
  for name in ORDER:
    if name != "expect" and name in meta.fields and not meta.one(name).strip():
      meta.errors.append(f"`@{name}:` is empty")

  technique = meta.one("technique")
  if technique and technique not in TECHNIQUES:
    meta.errors.append(f"`@technique: {technique}` is not one of {', '.join(TECHNIQUES)}")

  # House style: the block leads the file, is contiguous, and is in ORDER.
  numbers = [lineno for lineno, _ in seen]
  if numbers and numbers[0] != 1:
    meta.errors.append(f"the `@` block must start on line 1 (it starts on line {numbers[0]})")
  if numbers and numbers != list(range(numbers[0], numbers[0] + len(numbers))):
    meta.errors.append("the `@` block must be contiguous (no blank or prose lines inside it)")
  ranks = [ORDER.index(name) for _, name in seen]
  if ranks != sorted(ranks):
    meta.errors.append(f"fields must appear in the order: {', '.join(ORDER)}")

  return meta


# ---------------------------------------------------------------------------
# running the program
# ---------------------------------------------------------------------------


def _run(path: Path, store: bool, timeout: float) -> list[str]:
  result = subprocess.run(
    [sys.executable, "-m", "jana_py.cli", "--std", STD] + (["-s"] if store else []) + [str(path)],
    cwd=ROOT,
    capture_output=True,
    text=True,
    timeout=timeout,
  )
  if result.returncode != 0:
    message = (result.stderr or result.stdout).strip().splitlines()
    raise RuntimeError(f"exited with status {result.returncode}: {message[-1] if message else '(no message)'}")
  return [line.rstrip() for line in result.stdout.splitlines()]


def observe(path: Path, timeout: float = 60.0) -> tuple[list[str], list[str]]:
  """Return (all output lines with `-s`, just the store lines).

  The store half is found by difference: `-s` prints exactly what a plain run
  prints, then the store.  That is more robust than trying to tell a store line
  from a line the program printed itself.
  """
  full = _run(path, store=True, timeout=timeout)
  plain = _run(path, store=False, timeout=timeout)
  return full, full[len(plain):]


def diff_expect(expected: list[str], actual: list[str]) -> list[str]:
  """Describe every place the two line lists disagree."""
  problems = []
  for index in range(max(len(expected), len(actual))):
    want = expected[index] if index < len(expected) else None
    got = actual[index] if index < len(actual) else None
    if want == got:
      continue
    if want is None:
      problems.append(f"line {index + 1}: unexpected extra output {got!r}")
    elif got is None:
      problems.append(f"line {index + 1}: expected {want!r} but output ended")
    else:
      problems.append(f"line {index + 1}: expected {want!r} but got {got!r}")
  return problems


def check_file(path: Path) -> list[str]:
  """Return the problems with one file; empty means it is fine (or unannotated)."""
  problems: list[str] = []
  if not FILENAME_RE.match(path.name):
    problems.append(f"filename is not lowercase_with_underscores: {path.name}")

  meta = parse_meta(path)
  if not meta.annotated:
    return problems
  problems += meta.errors
  if "expect" not in meta.fields:
    return problems

  try:
    full, store_lines = observe(path)
  except (RuntimeError, subprocess.TimeoutExpired) as exc:
    return problems + [f"could not run the program: {exc}"]

  problems += diff_expect(meta.fields["expect"], full)

  oracle = meta.one("oracle")
  if not (oracle or meta.one("keep")):
    return problems
  try:
    store = parse_store(store_lines)
  except ValueError as exc:
    return problems + [f"the store could not be parsed, so @keep/@oracle cannot be checked: {exc}"]

  if oracle:
    ok, detail = evaluate_oracle(oracle, store)
    if not ok:
      problems.append(f"`@oracle: {oracle}` {detail}")

  problems += check_garbage(path, store, meta.one("keep"))
  return problems


def check_garbage(path: Path, store: dict[str, Any], keep_field: str) -> list[str]:
  """Check `@keep` against the run, and the `_g` suffix against the garbage."""
  problems = []
  keep = parse_keep(keep_field)
  unknown = [name for name in keep if name not in store]
  if unknown:
    problems.append(
      f"`@keep:` names {', '.join(unknown)}, which the final store does not have "
      f"(it has: {', '.join(store) or 'nothing'})")
  kept_trivial = [name for name in keep if name in store and is_trivial(store[name])]
  if kept_trivial:
    problems.append(
      f"`@keep:` names {', '.join(kept_trivial)}, which the run leaves all-zero -- "
      "keep lists what actually survives, so drop them or use `none`")

  garbage = garbage_of(store, keep)
  stem, suffix = path.stem[:-2], path.stem[-2:]
  if suffix not in (GARBAGE_SUFFIX, CLEAN_SUFFIX):
    problems.append(
      f"the name must end in `{GARBAGE_SUFFIX}` (leaves garbage) or `{CLEAN_SUFFIX}` (clean)")
  elif garbage and suffix != GARBAGE_SUFFIX:
    problems.append(
      f"the run leaves garbage ({', '.join(garbage)}) but the name ends in "
      f"`{CLEAN_SUFFIX}`: rename to {stem}{GARBAGE_SUFFIX}.ja, or add those to `@keep:`")
  elif not garbage and suffix != CLEAN_SUFFIX:
    problems.append(
      f"the name ends in `{GARBAGE_SUFFIX}` but the run leaves no garbage: "
      f"rename to {stem}{CLEAN_SUFFIX}.ja, or narrow `@keep:`")
  return problems


# ---------------------------------------------------------------------------
# header normalization
# ---------------------------------------------------------------------------

BANNER_RE = re.compile(r"^\s*/{4,}\s*$")


def normalized_text(text: str) -> str:
  """Rewrite a file's leading comment region into the house style.

  The `@` block first, then a `//` separator, then the original prose as `//`
  lines.  `/* ... */` banners and rows of slashes become plain `//` comments;
  no prose is dropped.  Everything from the first line of code onwards is
  untouched.
  """
  lines = text.splitlines()
  at_lines: list[str] = []
  prose: list[str] = []
  index = 0
  in_block = False

  while index < len(lines):
    line = lines[index]
    stripped = line.strip()
    if in_block:
      body = stripped
      if body.endswith("*/"):
        body, in_block = body[:-2].rstrip(), False
      body = re.sub(r"^\*+\s?", "", body)
      prose.append(f"// {body}".rstrip() if body.strip() else "//")
      index += 1
      continue
    if FIELD_RE.match(line):
      at_lines.append(line.strip())
      index += 1
      continue
    if BANNER_RE.match(line):
      index += 1
      continue
    if stripped.startswith("//"):
      # Only the one space that separates `//` from the text is dropped: prose
      # indentation carries meaning (numbered lists, aligned tables).
      body = stripped[2:]
      body = body[1:] if body.startswith(" ") else body
      prose.append(f"// {body}".rstrip() if body.strip() else "//")
      index += 1
      continue
    if stripped.startswith("/*"):
      body = stripped[2:]
      in_block = True
      if body.rstrip().endswith("*/"):
        body, in_block = body.rstrip()[:-2], False
      body = re.sub(r"^\*+\s?", "", body.strip())
      if body.strip():
        prose.append(f"// {body}".rstrip())
      index += 1
      continue
    if not stripped:
      index += 1
      continue
    break

  # Blank comment lines survive as paragraph breaks, but not doubled up and not
  # at either end of the block.
  collapsed: list[str] = []
  for line in prose:
    if line == "//" and (not collapsed or collapsed[-1] == "//"):
      continue
    collapsed.append(line)
  while collapsed and collapsed[-1] == "//":
    collapsed.pop()
  prose = collapsed
  ordered = [line for name in ORDER for line in at_lines if FIELD_RE.match(line).group(1) == name]
  ordered += [line for line in at_lines if line not in ordered]

  head = ordered + (["//"] if ordered and prose else []) + prose
  body = lines[index:]
  return "\n".join(head + ([""] if head else []) + body).rstrip() + "\n"


# ---------------------------------------------------------------------------
# commands
# ---------------------------------------------------------------------------


def targets(paths: list[str]) -> list[Path]:
  return [Path(p).resolve() for p in paths] if paths else sorted(EXAMPLES.glob("*.ja"))


def cmd_report(args: argparse.Namespace) -> int:
  files = targets(args.files)
  metas = {path: parse_meta(path) for path in files}
  annotated = [path for path, meta in metas.items() if meta.annotated]
  missing = [path for path in files if path not in annotated]

  print(f"annotated {len(annotated)}/{len(files)} ({100 * len(annotated) // max(len(files), 1)}%)")
  with_oracle = [path for path in annotated if metas[path].one("oracle")]
  print(f"with @oracle {len(with_oracle)}/{len(annotated) or 1}")

  tally: dict[str, int] = {}
  for path in annotated:
    key = metas[path].one("technique") or "(none)"
    tally[key] = tally.get(key, 0) + 1
  if tally:
    print("\nby technique:")
    for technique, count in sorted(tally.items(), key=lambda kv: -kv[1]):
      print(f"  {count:3d}  {technique}")

  # Files the annotator could not independently confirm: the ones most likely to
  # be genuinely wrong, and the reason a human is doing this rather than a script.
  unverified = [path for path in annotated if metas[path].one("confirmed").startswith("UNVERIFIED")]
  if unverified:
    print(f"\nUNVERIFIED -- needs a second look ({len(unverified)}):")
    for path in unverified:
      print(f"  {path.name}: {metas[path].one('confirmed')}")

  leaves_garbage = [path for path in files if path.stem.endswith(GARBAGE_SUFFIX)]
  print(f"\nleaves garbage `{GARBAGE_SUFFIX}` {len(leaves_garbage)}/{len(files)}, "
        f"clean `{CLEAN_SUFFIX}` {len(files) - len(leaves_garbage)}/{len(files)}")

  badly_named = [path for path in files if not FILENAME_RE.match(path.name)]
  if badly_named:
    print(f"\nnot lowercase_with_underscores ({len(badly_named)}):")
    for path in badly_named:
      print(f"  {path.name}")

  if missing and not args.quiet:
    print("\nnot yet annotated:")
    for path in missing:
      print(f"  {path.name}")
  return 0


def cmd_check(args: argparse.Namespace) -> int:
  files = targets(args.files)
  checked = failed = 0
  for path in files:
    if not parse_meta(path).annotated and FILENAME_RE.match(path.name):
      continue
    checked += 1
    problems = check_file(path)
    if problems:
      failed += 1
      print(f"FAIL {path.name}")
      for problem in problems:
        print(f"     {problem}")
  print(f"\nchecked {checked} file(s), {failed} failed")
  return 1 if failed else 0


def cmd_stub(args: argparse.Namespace) -> int:
  for path in targets(args.files):
    try:
      full, store_lines = observe(path)
    except (RuntimeError, subprocess.TimeoutExpired) as exc:
      print(f"// {path.name}: could not run -- {exc}", file=sys.stderr)
      return 1
    print(f"// ---- paste at the top of {path.name} ----")
    print("// @summary:   TODO one English line: what does this compute?")
    print(f"// @technique: TODO one of: {', '.join(TECHNIQUES)}")
    print("// @source:    TODO a citation, or `original`")
    print("// @confirmed: TODO how you checked the values below are the right ones")
    try:
      live = [name for name, value in parse_store(store_lines).items() if not is_trivial(value)]
      print(f"// @keep:      TODO which of these are input-or-answer (the rest is garbage): {', '.join(live) or KEEP_NONE}")
    except ValueError:
      print(f"// @keep:      TODO the variables that are input-or-answer, or `{KEEP_NONE}`")
    print("// @oracle:    TODO a Python expression that is True iff the answer is right -- or delete this line")
    for line in full:
      print(f"// @expect: {line}")
    if not full:
      print("// @expect:")
    sys.stdout.flush()
    try:
      print(f"\nnames @oracle can use: {_render(parse_store(store_lines))}", file=sys.stderr)
    except ValueError as exc:
      print(f"\nstore not parseable, so @oracle cannot be used here: {exc}", file=sys.stderr)
  return 0


def cmd_store(args: argparse.Namespace) -> int:
  for path in targets(args.files):
    _, store_lines = observe(path)
    store = parse_store(store_lines)
    keep = parse_keep(parse_meta(path).one("keep") or KEEP_NONE)
    print(f"{path.name}:")
    for name, value in store.items():
      if is_trivial(value):
        note = "  (all zero)"
      elif name in keep:
        note = "  <- @keep"
      else:
        note = "  <- GARBAGE" if keep else ""
      print(f"  {name} = {value}{note}")
  return 0


def cmd_normalize(args: argparse.Namespace) -> int:
  changed = 0
  for path in targets(args.files):
    text = path.read_text()
    fixed = normalized_text(text)
    if fixed != text:
      changed += 1
      if not args.dry_run:
        path.write_text(fixed)
      print(f"{'would rewrite' if args.dry_run else 'rewrote'} {path.name}")
  print(f"\n{changed} file(s)")
  return 0


def main() -> int:
  parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
  sub = parser.add_subparsers(dest="command", required=True)

  for name, handler, help_text in (
    ("report", cmd_report, "show how many files carry a metadata header"),
    ("check", cmd_check, "verify the headers, @expect and @oracle"),
    ("stub", cmd_stub, "print a header for a file, with @expect filled in"),
    ("store", cmd_store, "print the final store as @oracle sees it"),
    ("normalize", cmd_normalize, "rewrite comment headers into the house style"),
  ):
    child = sub.add_parser(name, help=help_text)
    child.add_argument("files", nargs="*", help="default: the whole example corpus")
    child.add_argument("-q", "--quiet", action="store_true", help="report: omit the list of unannotated files")
    child.add_argument("-n", "--dry-run", action="store_true", help="normalize: show what would change")
    child.set_defaults(handler=handler)

  args = parser.parse_args()
  return args.handler(args)


if __name__ == "__main__":
  sys.exit(main())
