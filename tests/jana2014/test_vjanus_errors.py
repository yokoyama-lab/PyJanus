"""Static error detection tests for `vjanus`.

Programs that are syntactically valid jana2014 but contain constructs that
vjanus rejects statically (before lowering) should exit 1, not exit 3.
Exit 3 means "unsupported feature" (corpus test skips); exit 1 means
"this program is erroneous" (corpus test would fail, and so should this).
"""
from __future__ import annotations

import subprocess
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
