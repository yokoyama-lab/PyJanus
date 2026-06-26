"""The bundled reversible standard library `std/bits.ja`.

Forward correctness AND reversibility for each bit utility, run through the CLI
so the packaged `#include "std/bits.ja"` resolution is exercised end to end.
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]


def run_store(src: str, tmp_path: Path) -> str:
  prog = tmp_path / "prog.ja"
  prog.write_text(src)
  proc = subprocess.run(
    [sys.executable, "-m", "jana_py.cli", "-s", str(prog)],
    cwd=ROOT, text=True, capture_output=True,
  )
  assert proc.returncode == 0, proc.stderr
  return proc.stdout


def _prog(body: str) -> str:
  return '#include "std/bits.ja"\nvoid main() {\n' + body + '}\n'


class TestFlipBit:

  def test_sets_a_clear_bit(self, tmp_path):
    out = run_store(_prog("    int x = 5;\n    call flip_bit(x, 1);\n"), tmp_path)
    assert "x = 7" in out            # 0b101 ^ 0b010 = 0b111

  def test_is_self_inverse(self, tmp_path):
    out = run_store(_prog(
      "    int x = 5;\n"
      "    call flip_bit(x, 1);\n"
      "    call flip_bit(x, 1);\n"), tmp_path)
    assert "x = 5" in out


class TestSwapBits:

  def test_swaps_differing_bits(self, tmp_path):
    out = run_store(_prog("    int y = 10;\n    call swap_bits(y, 0, 1);\n"), tmp_path)
    assert "y = 9" in out             # 0b1010 -> 0b1001

  def test_equal_bits_unchanged(self, tmp_path):
    out = run_store(_prog("    int z = 10;\n    call swap_bits(z, 1, 3);\n"), tmp_path)
    assert "z = 10" in out            # both bits are 1

  def test_is_self_inverse(self, tmp_path):
    out = run_store(_prog(
      "    int y = 10;\n"
      "    call swap_bits(y, 0, 2);\n"
      "    call swap_bits(y, 0, 2);\n"), tmp_path)
    assert "y = 10" in out


class TestBitReverse:

  def test_reverses_byte(self, tmp_path):
    out = run_store(_prog("    int a = 1;\n    call bit_reverse(a, 8);\n"), tmp_path)
    assert "a = 128" in out           # 0b00000001 -> 0b10000000

  def test_reverses_nibble(self, tmp_path):
    out = run_store(_prog("    int b = 13;\n    call bit_reverse(b, 4);\n"), tmp_path)
    assert "b = 11" in out            # 0b1101 -> 0b1011

  def test_roundtrip(self, tmp_path):
    out = run_store(_prog(
      "    int c = 13;\n"
      "    call bit_reverse(c, 4);\n"
      "    uncall bit_reverse(c, 4);\n"), tmp_path)
    assert "c = 13" in out

  def test_width_one_is_identity(self, tmp_path):
    out = run_store(_prog("    int d = 1;\n    call bit_reverse(d, 1);\n"), tmp_path)
    assert "d = 1" in out


class TestRotateBitsLeft:

  def test_shifts_bit_up(self, tmp_path):
    out = run_store(_prog("    int p = 1;\n    call rotate_bits_left(p, 4);\n"), tmp_path)
    assert "p = 2" in out             # 0b0001 -> 0b0010

  def test_top_bit_wraps(self, tmp_path):
    out = run_store(_prog("    int q = 8;\n    call rotate_bits_left(q, 4);\n"), tmp_path)
    assert "q = 1" in out             # 0b1000 -> 0b0001

  def test_roundtrip(self, tmp_path):
    out = run_store(_prog(
      "    int r = 11;\n"
      "    call rotate_bits_left(r, 4);\n"
      "    uncall rotate_bits_left(r, 4);\n"), tmp_path)
    assert "r = 11" in out


if __name__ == "__main__":
  raise SystemExit(pytest.main([__file__, "-q"]))
