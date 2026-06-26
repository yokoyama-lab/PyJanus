"""The bundled reversible standard library `std/array.ja`.

These tests pin both halves of the contract every library procedure must
satisfy: forward correctness AND reversibility (`call P; uncall P` restores the
store).  Programs are run through the CLI so the real `#include "std/array.ja"`
resolution (via the packaged stdlib search path) is exercised end to end.

`tmp_path` is used as the program's directory so the include is found through
the bundled-stdlib fallback, NOT a co-located copy.
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]


def run_store(src: str, tmp_path: Path, *extra_args: str) -> str:
  """Run `src` with `-s` from an unrelated dir; return the final-store text."""
  prog = tmp_path / "prog.ja"
  prog.write_text(src)
  proc = subprocess.run(
    [sys.executable, "-m", "jana_py.cli", "-s", *extra_args, str(prog)],
    cwd=ROOT, text=True, capture_output=True,
  )
  assert proc.returncode == 0, proc.stderr
  return proc.stdout


# ── reverse ────────────────────────────────────────────────────────────────

class TestReverse:

  def test_forward_reverses(self, tmp_path):
    out = run_store(
      '#include "std/array.ja"\n'
      'void main() {\n'
      '    int a[5] = {10, 20, 30, 40, 50};\n'
      '    call reverse(a, 5);\n'
      '}\n', tmp_path)
    assert "a[5] = {50, 40, 30, 20, 10}" in out

  def test_odd_length_keeps_middle(self, tmp_path):
    out = run_store(
      '#include "std/array.ja"\n'
      'void main() {\n'
      '    int a[3] = {1, 2, 3};\n'
      '    call reverse(a, 3);\n'
      '}\n', tmp_path)
    assert "a[3] = {3, 2, 1}" in out

  def test_reversible_roundtrip(self, tmp_path):
    out = run_store(
      '#include "std/array.ja"\n'
      'void main() {\n'
      '    int a[4] = {7, 8, 9, 10};\n'
      '    call reverse(a, 4);\n'
      '    uncall reverse(a, 4);\n'
      '}\n', tmp_path)
    assert "a[4] = {7, 8, 9, 10}" in out

  def test_singleton_is_identity(self, tmp_path):
    out = run_store(
      '#include "std/array.ja"\n'
      'void main() {\n'
      '    int a[1] = {42};\n'
      '    call reverse(a, 1);\n'
      '}\n', tmp_path)
    assert "a[1] = {42}" in out


# ── rotate_left ──────────────────────────────────────────────────────────────

class TestRotateLeft:

  def test_forward_rotates(self, tmp_path):
    out = run_store(
      '#include "std/array.ja"\n'
      'void main() {\n'
      '    int a[4] = {1, 2, 3, 4};\n'
      '    call rotate_left(a, 4);\n'
      '}\n', tmp_path)
    assert "a[4] = {2, 3, 4, 1}" in out

  def test_uncall_rotates_right(self, tmp_path):
    out = run_store(
      '#include "std/array.ja"\n'
      'void main() {\n'
      '    int a[4] = {1, 2, 3, 4};\n'
      '    uncall rotate_left(a, 4);\n'
      '}\n', tmp_path)
    assert "a[4] = {4, 1, 2, 3}" in out

  def test_reversible_roundtrip(self, tmp_path):
    out = run_store(
      '#include "std/array.ja"\n'
      'void main() {\n'
      '    int a[3] = {5, 6, 7};\n'
      '    call rotate_left(a, 3);\n'
      '    uncall rotate_left(a, 3);\n'
      '}\n', tmp_path)
    assert "a[3] = {5, 6, 7}" in out


# ── xor_into / add_into ─────────────────────────────────────────────────────

class TestElementwise:

  def test_add_into_forward(self, tmp_path):
    out = run_store(
      '#include "std/array.ja"\n'
      'void main() {\n'
      '    int d[3] = {5, 6, 7};\n'
      '    int s[3] = {1, 2, 3};\n'
      '    call add_into(d, s, 3);\n'
      '}\n', tmp_path)
    assert "d[3] = {6, 8, 10}" in out

  def test_add_into_uncall_subtracts(self, tmp_path):
    out = run_store(
      '#include "std/array.ja"\n'
      'void main() {\n'
      '    int d[3] = {6, 8, 10};\n'
      '    int s[3] = {1, 2, 3};\n'
      '    uncall add_into(d, s, 3);\n'
      '}\n', tmp_path)
    assert "d[3] = {5, 6, 7}" in out

  def test_xor_into_is_self_inverse(self, tmp_path):
    out = run_store(
      '#include "std/array.ja"\n'
      'void main() {\n'
      '    int d[3] = {5, 6, 7};\n'
      '    int s[3] = {1, 2, 3};\n'
      '    call xor_into(d, s, 3);\n'
      '    call xor_into(d, s, 3);\n'
      '}\n', tmp_path)
    assert "d[3] = {5, 6, 7}" in out


# ── cswap (robust reversible comparator) ────────────────────────────────────

class TestCswap:

  def test_swaps_when_out_of_order(self, tmp_path):
    out = run_store(
      '#include "std/array.ja"\n'
      'void main() {\n'
      '    int a = 5;\n'
      '    int b = 2;\n'
      '    int did;\n'
      '    call cswap(a, b, did);\n'
      '}\n', tmp_path)
    assert "a = 2" in out and "b = 5" in out
    assert "did = 1" in out          # flag records that a swap happened

  def test_robust_on_already_sorted_pair(self, tmp_path):
    # The value-only comparator `fi (x < y)` breaks its reversibility assertion
    # here; the flag-based one must run cleanly and leave the pair untouched.
    out = run_store(
      '#include "std/array.ja"\n'
      'void main() {\n'
      '    int a = 2;\n'
      '    int b = 5;\n'
      '    int did;\n'
      '    call cswap(a, b, did);\n'
      '}\n', tmp_path)
    assert "a = 2" in out and "b = 5" in out
    assert "did = 0" in out

  def test_uncall_restores_and_clears_flag(self, tmp_path):
    out = run_store(
      '#include "std/array.ja"\n'
      'void main() {\n'
      '    int a = 5;\n'
      '    int b = 2;\n'
      '    int did;\n'
      '    call cswap(a, b, did);\n'
      '    uncall cswap(a, b, did);\n'
      '}\n', tmp_path)
    assert "a = 5" in out and "b = 2" in out and "did = 0" in out


if __name__ == "__main__":
  raise SystemExit(pytest.main([__file__, "-q"]))
