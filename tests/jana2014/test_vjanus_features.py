"""Feature-coverage tests for `vjanus`, the standalone verified interpreter.

Two coverage points that used to be gaps in vjanus's jana2014 front end:

1. **Multiplicative update assignments `*=` / `/=`** are part of base jana2014
   (`parser_jana2014.py`) but have no counterpart in the verified frame core
   (`RevFrame.v` only has `OAdd/OSub/OXor`).  vjanus must report them as a clean
   "unsupported" (exit 3, so the conformance corpus *skips* such a program),
   NOT as a hard parse error (exit 1, which the corpus would treat as failure).

2. **Struct value initializers** `= {..}` — for a scalar struct, an array of
   structs, and a struct with array fields — are now lowered, so vjanus agrees
   with PyJanus on the resulting store.

Needs the `vjanus` binary (build with `bash coq/vjanus/build.sh`); skips if absent.
"""
from __future__ import annotations

import re
import subprocess
import sys
import tempfile
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
VJANUS = ROOT / "coq" / "vjanus" / "vjanus"

pytestmark = pytest.mark.skipif(
    not VJANUS.exists(), reason="vjanus not built (run coq/vjanus/build.sh)"
)


def _run_vjanus(src: str) -> subprocess.CompletedProcess[str]:
    with tempfile.NamedTemporaryFile("w", suffix=".ja", delete=True) as f:
        f.write(src)
        f.flush()
        return subprocess.run([str(VJANUS), "-s", f.name],
                              capture_output=True, text=True)


def _parse_store(out: str) -> dict[str, str]:
    """Normalise a `-s` store dump into {name: canonical-value-string}
    (whitespace-stripped), mirroring test_vjanus_corpus._parse_store."""
    d: dict[str, str] = {}
    for line in out.splitlines():
        line = line.strip()
        m = re.match(r"^(\w+)((?:\[\d+\])+)\s*=\s*(\{.*\})$", line)
        if m:
            d[m.group(1)] = re.sub(r"\s", "", m.group(3)); continue
        m = re.match(r"^(\w+)\s*=\s*(\{.*\})$", line)
        if m:
            d[m.group(1)] = re.sub(r"\s", "", m.group(2)); continue
        m = re.match(r"^(\w+)\s*=\s*(-?\d+)$", line)
        if m and not line.startswith(("Warning", "PyJanus")):
            d[m.group(1)] = m.group(2)
    return d


def _assert_agrees(src: str) -> dict[str, str]:
    vj = _run_vjanus(src)
    assert vj.returncode == 0, f"vjanus exit {vj.returncode}: {vj.stderr}"
    with tempfile.NamedTemporaryFile("w", suffix=".ja", delete=True) as f:
        f.write(src)
        f.flush()
        pj = subprocess.run(
            [sys.executable, "-m", "jana_py.cli", "--std", "jana2014", "-s", f.name],
            cwd=ROOT, capture_output=True, text=True,
        )
    assert pj.returncode == 0, pj.stderr
    got, want = _parse_store(vj.stdout), _parse_store(pj.stdout)
    diffs = {k: (got[k], want.get(k)) for k in got if got[k] != want.get(k)}
    assert not diffs, f"verified vs pyjanus differ: {diffs}"
    return got


# ---------------------------------------------------------------------------
# 1. `*=` / `/=` are cleanly unsupported (exit 3), not a hard parse error.
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("expr", ["1 << 3", "8 >> 1", "2 ** 3"])
def test_shift_and_power_are_unsupported_not_error(expr: str) -> None:
    """`<<` `>>` `**` are valid jana2014 (PyJanus supports them) but have no
    verified-core primitive; vjanus must skip cleanly (exit 3), not parse-error
    (exit 1).  They parse at the correct precedence, then lowering rejects them."""
    src = (
        "procedure main()\n"
        "    int x\n"
        f"    x += {expr}\n"
    )
    result = _run_vjanus(src)
    assert result.returncode == 3, (
        f"Expected exit 3 (unsupported), got {result.returncode}.\n"
        f"stdout: {result.stdout!r}\nstderr: {result.stderr!r}"
    )
    assert "operator" in result.stderr, (
        f"Expected an 'unsupported: operator …' message: {result.stderr!r}"
    )


@pytest.mark.parametrize("op", ["*=", "/="])
def test_multiplicative_update_is_unsupported_not_error(op: str) -> None:
    src = (
        "procedure main()\n"
        "    int x\n"
        "    x += 3\n"
        f"    x {op} 5\n"
    )
    result = _run_vjanus(src)
    assert result.returncode == 3, (
        f"Expected exit 3 (unsupported), got {result.returncode}.\n"
        f"stdout: {result.stdout!r}\nstderr: {result.stderr!r}"
    )
    assert "assign-op" in result.stderr and op in result.stderr, (
        f"Expected 'unsupported: assign-op {op}' message: {result.stderr!r}"
    )


# ---------------------------------------------------------------------------
# 2. Struct value initializers agree with PyJanus.
# ---------------------------------------------------------------------------

def test_scalar_struct_initializer() -> None:
    src = (
        "struct Point {\n"
        "    int x;\n"
        "    int y;\n"
        "};\n"
        "\n"
        "procedure main()\n"
        "    Point p = {3, 4}\n"
        "    Point q\n"
        "    q.x += p.x\n"
        "    q.y += p.y\n"
    )
    store = _assert_agrees(src)
    assert store["p"] == "{x=3,y=4}"
    assert store["q"] == "{x=3,y=4}"


def test_struct_array_initializer() -> None:
    src = (
        "struct Pair {\n"
        "    int a;\n"
        "    int b;\n"
        "};\n"
        "\n"
        "procedure main()\n"
        "    Pair v[2] = {{1, 2}, {3, 4}}\n"
        "    int s\n"
        "    s += v[0].a + v[1].b\n"
    )
    store = _assert_agrees(src)
    assert store["s"] == "5"


def test_flat_struct_array_field_initializer() -> None:
    src = (
        "struct Vec {\n"
        "    int tag;\n"
        "    int v[3];\n"
        "};\n"
        "\n"
        "procedure main()\n"
        "    Vec w = {7, {1, 2, 3}}\n"
        "    int s\n"
        "    s += w.tag + w.v[0] + w.v[2]\n"
    )
    store = _assert_agrees(src)
    assert store["s"] == "11"


# ---------------------------------------------------------------------------
# 3. Ternary `c ? t : e` and local arrays are supported; reversible read/write
#    (the jana2014_in_out I/O dialect) is cleanly unsupported (exit 3).
# ---------------------------------------------------------------------------

def test_ternary_expression_supported() -> None:
    src = (
        "procedure main()\n"
        "    int a\n"
        "    int b\n"
        "    int c\n"
        "    a += 5\n"
        "    b += (a > 3 ? 10 : 20)\n"    # true  -> 10
        "    c += (a > 9 ? 10 : 20)\n"    # false -> 20
    )
    store = _assert_agrees(src)
    assert store["b"] == "10"
    assert store["c"] == "20"


def test_logical_or_value_both_true() -> None:
    """`a || b` used as a value with both operands true must be 1, not 2.
    jana2014 requires boolean operands, so `||` lowers to `a + b - a*b` (OR),
    not the old `a*a + b*b` (= a + b, which gave 2).  Also exercised through the
    ternary, whose desugaring assumes a 0/1 condition."""
    src = (
        "procedure main()\n"
        "    int a\n"
        "    int b\n"
        "    int r\n"
        "    int t\n"
        "    a += 1\n"
        "    b += 1\n"
        "    r += (a > 0 || b > 0)\n"          # both true -> 1
        "    t += (a > 0 || b > 0 ? 5 : 9)\n"  # condition must be 0/1 -> 5
    )
    store = _assert_agrees(src)
    assert store["r"] == "1"
    assert store["t"] == "5"


def test_logical_and_value() -> None:
    """`&&` lowers to `l*r`, already correct for booleans."""
    src = (
        "procedure main()\n"
        "    int a\n"
        "    int b\n"
        "    int r\n"
        "    int u\n"
        "    a += 1\n"
        "    r += (a > 0 && a > 0)\n"    # 1
        "    u += (a > 0 && b > 0)\n"    # b=0 -> false -> 0
    )
    store = _assert_agrees(src)
    assert store["r"] == "1"
    assert store["u"] == "0"


def test_local_array_supported() -> None:
    """A `local int tmp[n]` lives in one depth-frame RL slot used as an array
    base; cleared to 0 before delocal, it agrees with PyJanus."""
    src = (
        "procedure work(int out[])\n"
        "    local int tmp[3]\n"
        "    tmp[0] += 5\n"
        "    tmp[1] += 7\n"
        "    out[0] += tmp[0]\n"
        "    out[1] += tmp[1]\n"
        "    tmp[0] -= out[0]\n"
        "    tmp[1] -= out[1]\n"
        "    delocal int tmp[3]\n"
        "procedure main()\n"
        "    int out[3]\n"
        "    call work(out)\n"
    )
    store = _assert_agrees(src)
    assert store["out"] == "{5,7,0}"


def test_io_read_write_is_unsupported() -> None:
    """`read`/`write` mutate the store, so vjanus must not silently drop them;
    the verified core has no I/O, so it skips cleanly (exit 3)."""
    src = (
        "procedure main()\n"
        "    int x\n"
        "    read x\n"
        "    x += 1\n"
        "    write x\n"
    )
    result = _run_vjanus(src)
    assert result.returncode == 3, (
        f"Expected exit 3 (unsupported), got {result.returncode}.\n"
        f"stdout: {result.stdout!r}\nstderr: {result.stderr!r}"
    )
    assert "read" in result.stderr or "I/O" in result.stderr, (
        f"Expected an I/O-unsupported message: {result.stderr!r}"
    )


if __name__ == "__main__":
    raise SystemExit(pytest.main([__file__, "-q"]))
