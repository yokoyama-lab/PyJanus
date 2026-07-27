"""Corpus-wide differential test: C++ code generator vs. the interpreter.

For every example program, generate C++, compile and run it at -O0, and compare
the final store to the interpreter.  The contract, in two halves:

  * **whatever the generator emits must compile** -- a `CFAIL` (g++ rejected the
    generated translation unit) is a *failure*, not a skip.  It used to be a
    skip, which quietly hid 14 broken programs out of 97: a procedure named
    `delete` colliding with the C++ keyword, an undeclared `unrank__inv`, and
    every program using a struct (the generator emitted `Point p = 0;`).
  * **and it must agree with the interpreter** -- a `WRONG` is a failure.

A construct the back-end knowingly cannot translate raises out of the generator
(`CGERR`) and is skipped with its reason; so is anything the harness cannot
compare (`SKIP`).  The distinction is the point: "I decline to translate this"
is honest, "here is some C++" followed by a compiler error is a bug.

Because C++ resolves every name, this test doubles as the static checker the
interpreter lacks -- it is what caught a call to an undefined procedure and a
procedure body using an undeclared variable, both in unreachable code that no
interpreter run could ever reach.

This is also the automated form of the cross-check that found six code-gen bugs
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
  if tag in ("CGERR", "SKIP"):
    # CGERR: the generator declined to translate a construct.  SKIP: the harness
    # cannot compare this store.  Neither is a claim about generated code.
    pytest.skip(f"{tag}: {msg}")
  assert tag != "CFAIL", (
    f"{Path(ja).name}: the generator emitted C++ that does not compile -- {msg}")
  assert tag == "PASS", f"{Path(ja).name}: {msg}"


def test_corpus_is_nonempty() -> None:
  assert EXAMPLES, "no example fixtures found"
