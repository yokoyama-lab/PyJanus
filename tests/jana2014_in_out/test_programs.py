"""Run jana2014_in_out test cases that are held as real Janus `.ja` files.

Each program in `programs/*.ja` carries its own I/O spec as `//` comments:

    // in:  3 7        # whitespace-separated stdin values (forward)
    // out: 7 3        # expected forward output values
    // error: <substr> # (optional) instead of out: forward must fail with <substr>

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

_SPEC_RE = re.compile(r"^\s*//\s*(in|out|error)\s*:\s*(.*?)\s*$")


def parse_spec(text: str) -> dict[str, str]:
  spec: dict[str, str] = {}
  for line in text.splitlines():
    m = _SPEC_RE.match(line)
    if m:
      spec[m.group(1)] = m.group(2)
  return spec


def run_program(path: Path, program_args: list[str], direction: str,
                expect: str | None = None) -> subprocess.CompletedProcess[str]:
  env = dict(os.environ)
  env["PYTHONPATH"] = str(ROOT)
  flags = ["--std", "jana2014_in_out", "--direction", direction]
  if expect is not None:
    flags += ["--expect", expect]
  return subprocess.run(
    [sys.executable, "-m", "jana_py.cli", *flags, str(path), *program_args],
    cwd=ROOT, text=True, capture_output=True, env=env, check=False,
  )


class ProgramFileTests(unittest.TestCase):
  pass


def _make_test(path: Path):
  def test(self: ProgramFileTests) -> None:
    spec = parse_spec(path.read_text(encoding="utf-8"))
    in_tokens = spec.get("in", "").split()

    if "error" in spec:
      result = run_program(path, in_tokens, "forward")
      self.assertNotEqual(result.returncode, 0, "expected the program to fail")
      self.assertIn(spec["error"], result.stdout)
      return

    self.assertIn("out", spec, f"{path.name} must declare `// out:` or `// error:`")
    out_tokens = spec["out"].split()

    forward = run_program(path, in_tokens, "forward", expect="\n".join(out_tokens))
    self.assertEqual(forward.returncode, 0, f"forward mismatch:\n{forward.stdout}{forward.stderr}")

    backward = run_program(
      path, list(reversed(out_tokens)), "backward", expect="\n".join(reversed(in_tokens))
    )
    self.assertEqual(backward.returncode, 0, f"backward mismatch:\n{backward.stdout}{backward.stderr}")

  return test


for _path in sorted(PROGRAMS.glob("*.ja")):
  setattr(ProgramFileTests, f"test_{_path.stem}", _make_test(_path))


if __name__ == "__main__":
  unittest.main()
