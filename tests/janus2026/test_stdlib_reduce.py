"""The bundled reversible standard library `std/reduce.ja`.

Each reduction accumulates into a zero-entering output and preserves its input
array, so `uncall` subtracts the result back out.  Forward correctness, input
preservation, reversibility, and the n == 0 no-op are all pinned here.
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
  return '#include "std/reduce.ja"\nvoid main() {\n' + body + '}\n'


class TestSumInto:

  def test_sums_and_preserves_input(self, tmp_path):
    out = run_store(_prog(
      "    int a[4] = {2, 4, 6, 8};\n    int s;\n"
      "    call sum_into(a, 4, s);\n"), tmp_path)
    assert "s = 20" in out
    assert "a[4] = {2, 4, 6, 8}" in out

  def test_roundtrip(self, tmp_path):
    out = run_store(_prog(
      "    int a[4] = {2, 4, 6, 8};\n    int s;\n"
      "    call sum_into(a, 4, s);\n"
      "    uncall sum_into(a, 4, s);\n"), tmp_path)
    assert "s = 0" in out

  def test_empty_is_noop(self, tmp_path):
    out = run_store(_prog(
      "    int a[3] = {0, 0, 0};\n    int s;\n"
      "    call sum_into(a, 0, s);\n"), tmp_path)
    assert "s = 0" in out


class TestDotInto:

  def test_dot_product(self, tmp_path):
    out = run_store(_prog(
      "    int a[4] = {2, 4, 6, 8};\n    int b[4] = {1, 0, 2, 1};\n    int dp;\n"
      "    call dot_into(a, b, 4, dp);\n"), tmp_path)
    assert "dp = 22" in out            # 2 + 0 + 12 + 8

  def test_roundtrip(self, tmp_path):
    out = run_store(_prog(
      "    int a[3] = {1, 2, 3};\n    int b[3] = {4, 5, 6};\n    int dp;\n"
      "    call dot_into(a, b, 3, dp);\n"
      "    uncall dot_into(a, b, 3, dp);\n"), tmp_path)
    assert "dp = 0" in out


class TestCountInto:

  def test_counts_matches(self, tmp_path):
    out = run_store(_prog(
      "    int a[5] = {4, 1, 4, 2, 4};\n    int cnt;\n"
      "    call count_into(a, 5, 4, cnt);\n"), tmp_path)
    assert "cnt = 3" in out

  def test_no_matches(self, tmp_path):
    out = run_store(_prog(
      "    int a[3] = {1, 2, 3};\n    int cnt;\n"
      "    call count_into(a, 3, 9, cnt);\n"), tmp_path)
    assert "cnt = 0" in out

  def test_roundtrip(self, tmp_path):
    out = run_store(_prog(
      "    int a[4] = {5, 5, 1, 5};\n    int cnt;\n"
      "    call count_into(a, 4, 5, cnt);\n"
      "    uncall count_into(a, 4, 5, cnt);\n"), tmp_path)
    assert "cnt = 0" in out


class TestMinMaxInto:
  """min/max are the history-needing reductions: flags + hist record enough to
  undo them, and the input array is preserved (never modified)."""

  def test_min_value_and_input_preserved(self, tmp_path):
    out = run_store(_prog(
      "    int a[5] = {3, 1, 4, 1, 5};\n"
      "    int m;\n    int flags[4];\n    stack hist;\n"
      "    call min_into(a, 5, m, flags, hist);\n"), tmp_path)
    assert "m = 1" in out
    assert "a[5] = {3, 1, 4, 1, 5}" in out

  def test_max_value(self, tmp_path):
    out = run_store(_prog(
      "    int a[5] = {3, 1, 4, 1, 5};\n"
      "    int m;\n    int flags[4];\n    stack hist;\n"
      "    call max_into(a, 5, m, flags, hist);\n"), tmp_path)
    assert "m = 5" in out

  def test_min_roundtrip_clears_history(self, tmp_path):
    out = run_store(_prog(
      "    int a[5] = {3, 1, 4, 1, 5};\n"
      "    int m;\n    int flags[4];\n    stack hist;\n"
      "    call min_into(a, 5, m, flags, hist);\n"
      "    uncall min_into(a, 5, m, flags, hist);\n"), tmp_path)
    assert "m = 0" in out
    assert "flags[4] = {0, 0, 0, 0}" in out
    assert "hist = nil" in out

  def test_max_roundtrip(self, tmp_path):
    out = run_store(_prog(
      "    int a[4] = {2, 9, 3, 9};\n"
      "    int m;\n    int flags[3];\n    stack hist;\n"
      "    call max_into(a, 4, m, flags, hist);\n"
      "    uncall max_into(a, 4, m, flags, hist);\n"), tmp_path)
    assert "m = 0" in out
    assert "hist = nil" in out

  def test_singleton(self, tmp_path):
    out = run_store(_prog(
      "    int a[1] = {42};\n"
      "    int m;\n    int flags[1];\n    stack hist;\n"
      "    call min_into(a, 1, m, flags, hist);\n"), tmp_path)
    assert "m = 42" in out


if __name__ == "__main__":
  raise SystemExit(pytest.main([__file__, "-q"]))
