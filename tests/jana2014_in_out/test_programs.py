"""Run jana2014_in_out test cases that are held as real Janus `.ja` files.

Each program in `programs/*.ja` carries its own I/O specs as `//` comments:

    // case: small    # optional; starts a named test case
    // in:  3 7        # whitespace-separated stdin values (forward)
    // out: 7 3        # expected forward output values
    // error: <substr> # (optional) instead of out: forward must fail with <substr>

Programs may declare multiple `case` blocks. For compatibility, files without
`case` comments are treated as a single default case.

Every program is executed through the PyJanus CLI (`python -m jana_py.cli`):
  * forward : stdin = `in`,           expected stdout = `out`
  * backward: stdin = reverse(`out`), expected stdout = reverse(`in`)

The reversal reflects reversible-I/O stream semantics: running a program
backward consumes its output stream in reverse and reproduces the input in
reverse, so `backward(reverse(out)) == reverse(in)`.
"""
from __future__ import annotations

import os
from pathlib import Path
import re
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
PROGRAMS = Path(__file__).resolve().parent / "programs"

_SPEC_RE = re.compile(r"^\s*//\s*(case|in|out|error)\s*:\s*(.*?)\s*$")


def parse_specs(text: str) -> list[dict[str, str]]:
  specs: list[dict[str, str]] = []
  spec: dict[str, str] = {"case": "default"}
  fields: set[str] = set()
  case_names: set[str] = set()
  errors: list[str] = []
  saw_field = False

  def finish_case(line_no: int) -> None:
    nonlocal fields, saw_field
    if not saw_field:
      return
    case_name = spec["case"]
    if case_name in case_names:
      errors.append(f"line {line_no}: duplicate case name {case_name!r}")
    case_names.add(case_name)
    if "in" not in fields:
      errors.append(f"line {line_no}: case {case_name!r} must declare `// in:`")
    if "out" in fields and "error" in fields:
      errors.append(f"line {line_no}: case {case_name!r} cannot declare both `// out:` and `// error:`")
    if "out" not in fields and "error" not in fields:
      errors.append(f"line {line_no}: case {case_name!r} must declare `// out:` or `// error:`")
    specs.append(spec.copy())
    fields = set()
    saw_field = False

  for line_no, line in enumerate(text.splitlines(), start=1):
    m = _SPEC_RE.match(line)
    if not m:
      continue

    key, value = m.group(1), m.group(2)
    if key == "case":
      finish_case(line_no)
      spec = {"case": value or f"case_{len(specs) + 1}"}
      continue

    if key in fields:
      errors.append(f"line {line_no}: duplicate `// {key}:` in case {spec['case']!r}")
    spec[key] = value
    fields.add(key)
    saw_field = True

  finish_case(len(text.splitlines()))
  if errors:
    raise ValueError("\n".join(errors))
  return specs


def run_program(path: Path, program_args: list[str], direction: str,
                expect: str | None = None) -> subprocess.CompletedProcess[str]:
  env = dict(os.environ)
  env["PYTHONPATH"] = str(ROOT)
  flags = ["--std", "jana2014_in_out", "--direction", direction]
  if expect is not None:
    # `--expect=` form: on Python < 3.13 argparse rejects a separate value
    # starting with `-` unless it parses as a plain negative number
    # (e.g. "-9\n3" -> "error: argument --expect: expected one argument").
    flags += [f"--expect={expect}"]
  return subprocess.run(
    [sys.executable, "-m", "jana_py.cli", *flags, str(path), *program_args],
    cwd=ROOT, text=True, capture_output=True, env=env, check=False,
  )


class ProgramFileTests(unittest.TestCase):
  pass


def _safe_test_name(value: str) -> str:
  name = re.sub(r"\W+", "_", value).strip("_")
  if not name:
    name = "case"
  if name[0].isdigit():
    name = f"_{name}"
  return name


def _make_case_test(path: Path, spec: dict[str, str]):
  def test(self: ProgramFileTests) -> None:
    in_tokens = spec.get("in", "").split()

    if "error" in spec:
      result = run_program(path, in_tokens, "forward")
      self.assertNotEqual(result.returncode, 0, "expected the program to fail")
      self.assertIn(spec["error"], result.stdout)
      return

    out_tokens = spec["out"].split()

    forward = run_program(path, in_tokens, "forward", expect="\n".join(out_tokens))
    self.assertEqual(forward.returncode, 0, f"forward mismatch:\n{forward.stdout}{forward.stderr}")

    backward = run_program(
      path, list(reversed(out_tokens)), "backward", expect="\n".join(reversed(in_tokens))
    )
    self.assertEqual(backward.returncode, 0, f"backward mismatch:\n{backward.stdout}{backward.stderr}")

  return test


def _make_invalid_spec_test(path: Path, exc: ValueError):
  def test(self: ProgramFileTests) -> None:
    self.fail(f"invalid I/O spec in {path.name}:\n{exc}")

  return test


for _path in sorted(PROGRAMS.glob("*.ja")):
  _program_name = _safe_test_name(_path.stem)
  try:
    _specs = parse_specs(_path.read_text(encoding="utf-8"))
  except ValueError as _exc:
    setattr(ProgramFileTests, f"test_{_program_name}__invalid_spec", _make_invalid_spec_test(_path, _exc))
    continue

  if not _specs:
    _exc = ValueError(f"{_path.name} must declare at least one I/O spec")
    setattr(ProgramFileTests, f"test_{_program_name}__invalid_spec", _make_invalid_spec_test(_path, _exc))
    continue

  _used_names: set[str] = set()
  for _index, _spec in enumerate(_specs, start=1):
    _case_name = _safe_test_name(_spec["case"])
    if _case_name in _used_names:
      _case_name = f"{_case_name}_{_index}"
    _used_names.add(_case_name)
    setattr(ProgramFileTests, f"test_{_program_name}__{_case_name}", _make_case_test(_path, _spec))


if __name__ == "__main__":
  unittest.main()
