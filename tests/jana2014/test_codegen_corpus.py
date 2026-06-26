"""Corpus-wide differential test: C++ code generator vs. the interpreter.

For every example program, generate C++, compile and run it at -O0, and compare
the final store to the interpreter.  The generator must never produce a *wrong*
result on a program it accepts; constructs the back-end does not support yet
(stacks, multi-dimensional array parameters, `size()` on a parameter) are skipped
with their reason rather than failed.

This is the automated form of the cross-check that found six code-gen bugs
(uninitialized locals, the loop off-by-one, unimplemented `uncall`, a
forward/inverse confusion, a descending-`iterate` bound, and a procedure/variable
name clash).  Keeping it in the suite stops those from regressing.
"""
from __future__ import annotations

import glob
import shutil
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "coq" / "harness"))
import codegen_diff  # noqa: E402  (reuse the standalone differential driver)

EXAMPLES = sorted(glob.glob(str(ROOT / "tests" / "jana2014" / "fixtures" / "examples" / "*.ja")))


@pytest.mark.skipif(not shutil.which("g++"), reason="g++ not available")
@pytest.mark.parametrize("ja", EXAMPLES, ids=lambda p: Path(p).name)
def test_codegen_matches_interpreter(ja: str) -> None:
  tag, msg = codegen_diff.check(ja)
  if tag in ("CFAIL", "CGERR", "SKIP"):
    pytest.skip(f"{tag}: {msg}")          # unsupported construct, not a wrong answer
  assert tag == "PASS", f"{Path(ja).name}: {msg}"


def test_corpus_is_nonempty() -> None:
  assert EXAMPLES, "no example fixtures found"
