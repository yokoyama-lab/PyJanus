"""`#include` search-path resolution (bundled stdlib + `-I` directories).

`preprocess_text` resolves an include first relative to the including file, then
against each search directory: the user's `-I` dirs, then the packaged stdlib
(`jana_py/lib`).  These tests cover all three resolution routes and the
not-found error, at the preprocessor level (fast, no parsing).
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import pytest

from jana_py.errors import JanaError
from jana_py.preprocess import STDLIB_DIR, preprocess_text

ROOT = Path(__file__).resolve().parents[2]


def test_bundled_stdlib_is_resolved_from_any_cwd():
  # No -I, file lives in an unrelated dir: the include must still be found via
  # the packaged stdlib fallback.
  pp = preprocess_text("/nowhere/prog.ja", '#include "std/array.ja"\n')
  assert "void reverse" in pp.text


def test_stdlib_dir_points_at_packaged_library():
  assert (STDLIB_DIR / "std" / "array.ja").exists()


def test_dash_capital_i_directory_takes_precedence(tmp_path):
  libdir = tmp_path / "mylib"
  libdir.mkdir()
  (libdir / "greet.ja").write_text("void greet(int x) {\n    x += 1;\n}\n")
  pp = preprocess_text("/nowhere/prog.ja", '#include "greet.ja"\n',
                       include_dirs=[libdir])
  assert "void greet" in pp.text


def test_relative_include_still_works(tmp_path):
  (tmp_path / "helper.ja").write_text("void h(int x) {\n    x += 1;\n}\n")
  prog = tmp_path / "prog.ja"
  prog.write_text('#include "helper.ja"\n')
  pp = preprocess_text(str(prog), prog.read_text())
  assert "void h" in pp.text


def test_missing_include_raises():
  with pytest.raises(JanaError, match="not found"):
    preprocess_text("/nowhere/prog.ja", '#include "does/not/exist.ja"\n')


def test_cli_minus_capital_i_flag_end_to_end(tmp_path):
  # A program that includes a user library found only via -I, run forward.
  libdir = tmp_path / "lib"
  libdir.mkdir()
  (libdir / "inc.ja").write_text("void inc(int x) {\n    x += 1;\n}\n")
  prog = tmp_path / "prog.ja"
  prog.write_text(
    '#include "inc.ja"\n'
    'void main() {\n'
    '    int n;\n'
    '    call inc(n);\n'
    '}\n')
  proc = subprocess.run(
    [sys.executable, "-m", "jana_py.cli", "-I", str(libdir), "-s", str(prog)],
    cwd=ROOT, text=True, capture_output=True,
  )
  assert proc.returncode == 0, proc.stderr
  assert "n = 1" in proc.stdout


if __name__ == "__main__":
  raise SystemExit(pytest.main([__file__, "-q"]))
