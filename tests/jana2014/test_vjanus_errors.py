"""Static error detection tests for `vjanus`.

Programs that are syntactically valid jana2014 but contain constructs that
vjanus rejects statically (before lowering) should exit 1, not exit 3.
Exit 3 means "unsupported feature" (corpus test skips); exit 1 means
"this program is erroneous" (corpus test would fail, and so should this).
"""
from __future__ import annotations

import subprocess
import tempfile
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
VJANUS = ROOT / "coq" / "vjanus" / "vjanus"
ERRORS = ROOT / "tests" / "jana2014" / "fixtures_errors"


@pytest.mark.skipif(not VJANUS.exists(),
                    reason="vjanus not built (run coq/vjanus/build.sh)")
def test_self_referential_delocal_is_error() -> None:
    """Non-counter-idiom self-referential delocal must be rejected with exit 1."""
    result = subprocess.run(
        [str(VJANUS), "-s", str(ERRORS / "vjanus-delocal-self-ref.ja")],
        capture_output=True, text=True,
    )
    assert result.returncode == 1, (
        f"Expected exit 1 (static error), got {result.returncode}.\n"
        f"stdout: {result.stdout!r}\n"
        f"stderr: {result.stderr!r}"
    )
    assert "delocal" in result.stderr.lower() or "self-referential" in result.stderr.lower(), (
        f"Expected error message mentioning 'delocal' or 'self-referential': {result.stderr!r}"
    )


@pytest.mark.skipif(not VJANUS.exists(),
                    reason="vjanus not built (run coq/vjanus/build.sh)")
def test_binary_bitwise_operator_is_unsupported_not_parse_error() -> None:
    """A binary bitwise operator (`^`/`&`/`|`) in an expression is a feature the
    verified core lacks (it has XOR only as the `^=` assignment operator), so it
    must parse and then exit 3 ("unsupported") -- a clean feature gap the corpus
    test skips -- rather than exit 1 with a misleading "expected statement" parse
    error on a perfectly valid jana2014 program."""
    prog = (
        "procedure main()\n"
        "    int x\n"
        "    int y\n"
        "    x += 6\n"
        "    y += x ^ 3\n"
    )
    with tempfile.NamedTemporaryFile("w", suffix=".ja", delete=True) as f:
        f.write(prog)
        f.flush()
        result = subprocess.run(
            [str(VJANUS), "-s", f.name],
            capture_output=True, text=True,
        )
    assert result.returncode == 3, (
        f"Expected exit 3 (unsupported feature), got {result.returncode}.\n"
        f"stdout: {result.stdout!r}\n"
        f"stderr: {result.stderr!r}"
    )
    assert "operator" in result.stderr.lower() or "unsupported" in result.stderr.lower(), (
        f"Expected an 'unsupported operator' message: {result.stderr!r}"
    )
