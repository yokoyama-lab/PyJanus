"""The bundled reversible standard library `std/math.ja`.

Covers the accumulator primitives (which preserve their inputs) and the
showcase reversible Euclidean gcd, whose quotient-stack history makes the whole
computation undoable: forward gcd transforms (a, b) -> (gcd, 0) with quotients
on the stack, and `uncall gcd` consumes that history to restore (a, b).
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
  return '#include "std/math.ja"\nvoid main() {\n' + body + '}\n'


class TestMulAcc:

  def test_accumulates_product_preserving_inputs(self, tmp_path):
    out = run_store(_prog(
      "    int a = 6;\n    int b = 7;\n    int acc;\n"
      "    call mul_acc(a, b, acc);\n"), tmp_path)
    assert "acc = 42" in out
    assert "a = 6" in out and "b = 7" in out

  def test_uncall_subtracts(self, tmp_path):
    out = run_store(_prog(
      "    int a = 6;\n    int b = 7;\n    int acc = 42;\n"
      "    uncall mul_acc(a, b, acc);\n"), tmp_path)
    assert "acc = 0" in out


class TestDivmod:

  def test_quotient_and_remainder(self, tmp_path):
    out = run_store(_prog(
      "    int n = 23;\n    int d = 5;\n    int q;\n    int r;\n"
      "    call divmod(n, d, q, r);\n"), tmp_path)
    assert "q = 4" in out and "r = 3" in out
    assert "n = 23" in out and "d = 5" in out

  def test_roundtrip(self, tmp_path):
    out = run_store(_prog(
      "    int n = 23;\n    int d = 5;\n    int q;\n    int r;\n"
      "    call divmod(n, d, q, r);\n"
      "    uncall divmod(n, d, q, r);\n"), tmp_path)
    assert "q = 0" in out and "r = 0" in out


class TestReversibleGcd:

  def test_computes_gcd_and_quotient_history(self, tmp_path):
    out = run_store(_prog(
      "    int a = 12;\n    int b = 8;\n    stack hist;\n"
      "    call gcd(a, b, hist);\n"), tmp_path)
    assert "a = 4" in out and "b = 0" in out
    assert "hist = <2, 1]" in out          # quotients, top of stack first

  def test_coprime_inputs(self, tmp_path):
    out = run_store(_prog(
      "    int a = 9;\n    int b = 4;\n    stack hist;\n"
      "    call gcd(a, b, hist);\n"), tmp_path)
    assert "a = 1" in out and "b = 0" in out

  def test_uncall_restores_inputs_and_empties_history(self, tmp_path):
    out = run_store(_prog(
      "    int a = 12;\n    int b = 8;\n    stack hist;\n"
      "    call gcd(a, b, hist);\n"
      "    uncall gcd(a, b, hist);\n"), tmp_path)
    assert "a = 12" in out and "b = 8" in out
    assert "hist = nil" in out

  def test_already_terminal_b_zero_does_nothing(self, tmp_path):
    out = run_store(_prog(
      "    int a = 7;\n    int b = 0;\n    stack hist;\n"
      "    call gcd(a, b, hist);\n"), tmp_path)
    assert "a = 7" in out and "b = 0" in out
    assert "hist = nil" in out


if __name__ == "__main__":
  raise SystemExit(pytest.main([__file__, "-q"]))
