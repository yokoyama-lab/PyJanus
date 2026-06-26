"""The bundled reversible standard library `std/sort.ja`.

A reversible bubble sort: it records each comparison's swap decision in `flags`
(1 = swapped), which is the history that makes the sort undoable.  `uncall sort`
replays the decisions backwards to restore the original order and clear `flags`.

`flags` must enter all-zero with n*(n-1)/2 entries.  The already-sorted case is
the robustness check: a value-only comparator would break its reversibility
assertion there, but the flag-based one leaves flags all-zero and succeeds.
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
  return '#include "std/sort.ja"\nvoid main() {\n' + body + '}\n'


class TestSort:

  def test_sorts_ascending(self, tmp_path):
    out = run_store(_prog(
      "    int a[5] = {3, 1, 4, 1, 5};\n    int flags[10];\n"
      "    call sort(a, 5, flags);\n"), tmp_path)
    assert "a[5] = {1, 1, 3, 4, 5}" in out

  def test_records_swap_history(self, tmp_path):
    # A reverse-sorted array swaps on every comparison: flags all 1.
    out = run_store(_prog(
      "    int a[4] = {4, 3, 2, 1};\n    int flags[6];\n"
      "    call sort(a, 4, flags);\n"), tmp_path)
    assert "a[4] = {1, 2, 3, 4}" in out
    assert "flags[6] = {1, 1, 1, 1, 1, 1}" in out

  def test_already_sorted_is_robust(self, tmp_path):
    # The robustness case: no swaps, flags stay zero, no reversibility-assertion
    # failure (which a value-only `fi (a[j] < a[j+1])` comparator would hit).
    out = run_store(_prog(
      "    int a[4] = {1, 2, 3, 4};\n    int flags[6];\n"
      "    call sort(a, 4, flags);\n"), tmp_path)
    assert "a[4] = {1, 2, 3, 4}" in out
    assert "flags[6] = {0, 0, 0, 0, 0, 0}" in out

  def test_roundtrip_restores_order_and_clears_flags(self, tmp_path):
    out = run_store(_prog(
      "    int a[5] = {3, 1, 4, 1, 5};\n    int flags[10];\n"
      "    call sort(a, 5, flags);\n"
      "    uncall sort(a, 5, flags);\n"), tmp_path)
    assert "a[5] = {3, 1, 4, 1, 5}" in out
    assert "flags[10] = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0}" in out

  def test_singleton_and_pair(self, tmp_path):
    out = run_store(_prog(
      "    int one[1] = {7};\n    int f1[1];\n"
      "    int two[2] = {9, 2};\n    int f2[1];\n"
      "    call sort(one, 1, f1);\n"
      "    call sort(two, 2, f2);\n"), tmp_path)
    assert "one[1] = {7}" in out
    assert "two[2] = {2, 9}" in out
    assert "f2[1] = {1}" in out


if __name__ == "__main__":
  raise SystemExit(pytest.main([__file__, "-q"]))
