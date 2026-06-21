"""The bundled reversible standard library `std/stack.ja`.

copy_top reads the top of a stack non-destructively (uncall subtracts), and
move_all drains one stack onto an empty one (reversing order); `uncall move_all`
moves them back.  The interpreter prints a stack top-first as `<t, .., b]`.
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
  return '#include "std/stack.ja"\nvoid main() {\n' + body + '}\n'


class TestCopyTop:

  def test_reads_top_without_disturbing_stack(self, tmp_path):
    out = run_store(_prog(
      "    stack s;\n    int a = 3;\n    int b = 7;\n    int x;\n"
      "    push(a, s);\n    push(b, s);\n"
      "    call copy_top(s, x);\n"), tmp_path)
    assert "x = 7" in out             # top of s
    assert "s = <7, 3]" in out        # stack unchanged

  def test_uncall_subtracts_back(self, tmp_path):
    out = run_store(_prog(
      "    stack s;\n    int a = 7;\n    int x;\n"
      "    push(a, s);\n"
      "    call copy_top(s, x);\n"
      "    uncall copy_top(s, x);\n"), tmp_path)
    assert "x = 0" in out
    assert "s = <7]" in out


class TestMoveAll:

  def test_drains_and_reverses_order(self, tmp_path):
    out = run_store(_prog(
      "    stack src;\n    stack dst;\n"
      "    int a = 1;\n    int b = 2;\n    int c = 3;\n"
      "    push(a, src);\n    push(b, src);\n    push(c, src);\n"
      "    call move_all(src, dst);\n"), tmp_path)
    # src was <3, 2, 1]; draining reverses it onto dst.
    assert "dst = <1, 2, 3]" in out
    assert "src = nil" in out

  def test_roundtrip_restores_src(self, tmp_path):
    out = run_store(_prog(
      "    stack src;\n    stack dst;\n"
      "    int a = 1;\n    int b = 2;\n    int c = 3;\n"
      "    push(a, src);\n    push(b, src);\n    push(c, src);\n"
      "    call move_all(src, dst);\n"
      "    uncall move_all(src, dst);\n"), tmp_path)
    assert "src = <3, 2, 1]" in out
    assert "dst = nil" in out

  def test_empty_src_is_noop(self, tmp_path):
    out = run_store(_prog(
      "    stack src;\n    stack dst;\n"
      "    call move_all(src, dst);\n"), tmp_path)
    assert "src = nil" in out and "dst = nil" in out


if __name__ == "__main__":
  raise SystemExit(pytest.main([__file__, "-q"]))
