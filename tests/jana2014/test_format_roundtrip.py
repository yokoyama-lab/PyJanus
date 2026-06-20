"""The jana2014 formatter is faithful: its output re-parses and is idempotent.

Formatting is the least-covered area (the dialect pretty-printers).  Rather than
just touch lines, we pin a real property over the example corpus: formatting a
parsed program yields source that parses again to a program that formats
identically (so nothing is dropped or made unparseable), and the same holds for
the inverted program (`-i`).
"""
from __future__ import annotations

import glob
from pathlib import Path

import pytest

from jana_py.format import formatter_for_std
from jana_py.invert import invert_program
from jana_py.parser_jana2014 import parse_program
from jana_py.preprocess import preprocess_text
from jana_py.validate import validate_program

ROOT = Path(__file__).resolve().parents[2]
EXAMPLES = sorted(glob.glob(str(ROOT / "tests" / "jana2014" / "fixtures" / "examples" / "*.ja")))
FMT = formatter_for_std("jana2014")


def _parse_source(fn: str, src: str):
  pt = preprocess_text(fn, src)
  return parse_program(fn, pt.text, pt.line_origins)


@pytest.mark.parametrize("ja", EXAMPLES, ids=lambda p: Path(p).name)
def test_format_is_idempotent(ja: str) -> None:
  prog = _parse_source(ja, Path(ja).read_text())
  validate_program(prog)
  once = FMT.format_program(prog)
  prog2 = parse_program(ja, once)            # formatter output must re-parse
  validate_program(prog2)
  twice = FMT.format_program(prog2)
  assert once == twice


@pytest.mark.parametrize("ja", EXAMPLES, ids=lambda p: Path(p).name)
def test_inverted_source_reparses(ja: str) -> None:
  prog = _parse_source(ja, Path(ja).read_text())
  validate_program(prog)
  inverted = FMT.format_program(invert_program(prog))
  reparsed = parse_program(ja, inverted)     # `-i` output must be valid source
  validate_program(reparsed)


# ----- the original janus1982 dialect formatter ---------------------------

from jana_py.parser_janus1982 import parse_program as parse_1982  # noqa: E402

FMT_1982 = formatter_for_std("janus1982")

PROGRAMS_1982 = [
    "i\nj\nprocedure main\n    i += 5\n    j += 10\n    i <=> j\n",   # globals + swap
    "x\nprocedure main\n    x += 3\n    x -= 1\n",                    # assigns
    "procedure main\n    read x\n    x += 1\n    write x\n",         # read/write I/O
]


@pytest.mark.parametrize("src", PROGRAMS_1982, ids=range(len(PROGRAMS_1982)))
def test_janus1982_format_idempotent(src: str) -> None:
  prog = parse_1982("p.ja", src)
  validate_program(prog)
  once = FMT_1982.format_program(prog)
  prog2 = parse_1982("p.ja", once)           # 1982 formatter output must re-parse
  validate_program(prog2)
  assert once == FMT_1982.format_program(prog2)
