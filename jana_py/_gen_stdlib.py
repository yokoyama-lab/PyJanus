"""Generate per-dialect copies of the bundled standard library.

The library is authored once, in janus2026 (`jana_py/lib/std/*.ja`).  Copies for
other dialects are produced *mechanically*: parse the janus2026 source to the
shared AST, then re-emit it with that dialect's formatter (`formatter_for_std`).
There is thus a single source of truth — the janus2026 files — and the dialect
copies (`jana_py/lib/<dialect>/std/*.ja`) are derived artifacts.

Run `python -m jana_py._gen_stdlib` to (re)write the copies.  The test
`tests/janus2026/test_stdlib_dialects.py` asserts they are up to date and that
each copy computes the same store as the janus2026 original.
"""
from __future__ import annotations

from pathlib import Path

from .format import formatter_for_std
from .parser_janus2026 import parse_program
from .preprocess import STDLIB_DIR, preprocess_text

# Dialects we ship a generated stdlib for.  janus2026 is the source, not a copy.
DIALECTS = ["jana2014"]
SRC_DIR = STDLIB_DIR / "std"


def render(dialect: str, ja_path: Path) -> str:
  """Re-emit one janus2026 library file as `dialect` source."""
  src = ja_path.read_text(encoding="utf-8")
  pp = preprocess_text(str(ja_path), src)
  program = parse_program(ja_path.name, pp.text, pp.line_origins)
  body = formatter_for_std(dialect).format_program(program)
  banner = (
    f"// GENERATED from std/{ja_path.name} by `python -m jana_py._gen_stdlib`.\n"
    f"// Do not edit; edit the janus2026 source and regenerate.  Docs live there.\n\n"
  )
  return banner + body


def generate(dialect: str) -> dict[str, str]:
  """Map library file name -> generated `dialect` source."""
  return {p.name: render(dialect, p) for p in sorted(SRC_DIR.glob("*.ja"))}


def write_all() -> list[Path]:
  written: list[Path] = []
  for dialect in DIALECTS:
    outdir = STDLIB_DIR / dialect / "std"
    outdir.mkdir(parents=True, exist_ok=True)
    for name, text in generate(dialect).items():
      path = outdir / name
      path.write_text(text, encoding="utf-8")
      written.append(path)
  return written


if __name__ == "__main__":
  for p in write_all():
    print(f"wrote {p.relative_to(STDLIB_DIR.parent)}")
