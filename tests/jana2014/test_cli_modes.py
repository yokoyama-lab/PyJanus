"""Smoke tests for every CLI mode.

The CLI dispatches to the interpreter, inverter, AST/JSON dump, C++ codegen,
debugger, modular arithmetic, the inverse-store solver, and the circuit/pebble
research tools.  These exercise each mode end-to-end (and so a good slice of
`cli.py` and the tool modules) and catch regressions that crash a mode.
"""
from __future__ import annotations

import json
import subprocess
import sys

import pytest

PROG = (
    "procedure main()\n"
    "    int x\n"
    "    int y\n"
    "    x += 5\n"
    "    y += 3\n"
    "    x += y\n"
)


def cli(args, inp=None):
  return subprocess.run([sys.executable, "-m", "jana_py.cli", "--std", "jana2014", *args],
                        capture_output=True, text=True, input=inp)


@pytest.fixture
def prog(tmp_path):
  p = tmp_path / "p.ja"
  p.write_text(PROG)
  return str(p)


def test_run_forward(prog):
  r = cli(["-s", prog])
  assert r.returncode == 0, r.stderr
  assert "x = 8" in r.stdout and "y = 3" in r.stdout


def test_invert_source(tmp_path):
  # `-i` inverts procedure bodies (keeping main as the driver), so the inverse of
  # `a += 5` appears as `a -= 5`.
  p = tmp_path / "q.ja"
  p.write_text("procedure inc(int a)\n    a += 5\nprocedure main()\n    int x\n    call inc(x)\n")
  r = cli(["-i", str(p)])
  assert r.returncode == 0, r.stderr
  assert "a -= 5" in r.stdout


def test_ast_json(prog):
  r = cli(["-a", prog])
  assert r.returncode == 0, r.stderr
  json.loads(r.stdout)               # well-formed JSON AST


def test_codegen(prog):
  r = cli(["-c", prog])
  assert r.returncode == 0, r.stderr
  assert "int main()" in r.stdout


def test_debugger(prog):
  r = cli(["-d", prog])
  assert r.returncode == 0, r.stderr
  assert r.stdout.strip()            # produces a trace


def test_modular_bits(prog):
  r = cli(["-m", "8", "-s", prog])
  assert r.returncode == 0, r.stderr
  assert "x = 8" in r.stdout         # 8 fits in 8 bits


def test_modular_prime(prog):
  r = cli(["-p", "7", "-s", prog])
  assert r.returncode == 0, r.stderr
  assert "x = 1" in r.stdout         # 8 mod 7 = 1


def test_inverse_store(prog):
  # `--inverse` solves the initial store from a final one; output is JSON.
  r = cli(["--inverse", json.dumps({"x": 8, "y": 3}), prog])
  assert r.returncode == 0, r.stderr
  assert json.loads(r.stdout) == {"x": 0, "y": 0}


def test_circuit(prog):
  r = cli(["--circuit", prog])
  assert r.returncode == 0, r.stderr
  assert r.stdout.strip()


def test_profile(prog):
  r = cli(["--profile", prog])
  assert r.returncode == 0, r.stderr
  assert r.stdout.strip()
