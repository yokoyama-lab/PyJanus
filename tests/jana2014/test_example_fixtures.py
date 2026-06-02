from __future__ import annotations

import os
from pathlib import Path
import subprocess
import sys
import unittest


ROOT = Path(__file__).resolve().parents[2]
EXAMPLE_DIR = ROOT / "tests" / "jana2014" / "fixtures" / "examples"


def run_ast(path: Path) -> subprocess.CompletedProcess[str]:
  env = dict(os.environ)
  env["PYTHONPATH"] = str(ROOT)
  return subprocess.run(
    [sys.executable, "-m", "jana_py.cli", "--std", "jana2014", "-a", str(path)],
    cwd=ROOT,
    text=True,
    capture_output=True,
    env=env,
    check=False,
  )


def run_program(path: Path) -> subprocess.CompletedProcess[str]:
  env = dict(os.environ)
  env["PYTHONPATH"] = str(ROOT)
  return subprocess.run(
    [sys.executable, "-m", "jana_py.cli", "--std", "jana2014", str(path)],
    cwd=ROOT,
    text=True,
    capture_output=True,
    env=env,
    check=False,
  )


class ExampleFixtureTests(unittest.TestCase):
  def test_all_migrated_examples_parse(self) -> None:
    for path in sorted(EXAMPLE_DIR.glob("*.ja")):
      with self.subTest(path=path.name):
        result = run_ast(path)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


class AdaptedExampleTests(unittest.TestCase):
  """End-to-end runs of examples adapted from upstream Janus repositories."""

  def test_fall_recovers_initial_height_via_uncall(self) -> None:
    result = run_program(EXAMPLE_DIR / "fall.ja")
    self.assertEqual(result.returncode, 0, result.stderr)
    self.assertIn("h_r = 80", result.stdout)

  def test_fib_variants_all_compute_fib_four(self) -> None:
    result = run_program(EXAMPLE_DIR / "fib_variants.ja")
    self.assertEqual(result.returncode, 0, result.stderr)
    self.assertIn("fib  pair: x1=5 x2=8", result.stdout)
    self.assertIn("fiba: r=5 n=4 x1=0 x2=0", result.stdout)
    # fibb is fully garbage-free: it also clears n.
    self.assertIn("fibb: r=5 n=0 x1=0 x2=0", result.stdout)

  def test_injective_basics_staircase(self) -> None:
    result = run_program(EXAMPLE_DIR / "injective_basics.ja")
    self.assertEqual(result.returncode, 0, result.stderr)
    self.assertIn("inc:        x=6", result.stdout)
    self.assertIn("neg:        x=-6", result.stdout)
    self.assertIn("add:        x=-6 y=4", result.stdout)
    self.assertIn("dbl:        y=8", result.stdout)
    self.assertIn("mul_const:  y=24 (n=3)", result.stdout)
    self.assertIn("mul:        c=28", result.stdout)
    self.assertIn("square:     sq=36", result.stdout)
    # Cantor pairing pi(3, 4) = (3+4)(3+4+1)/2 + 3 = 28 + 3 = 31
    self.assertIn("cantor:     z=31", result.stdout)

  def test_injective_iterate_cumsum_xor_feistel(self) -> None:
    result = run_program(EXAMPLE_DIR / "injective_iterate.ja")
    self.assertEqual(result.returncode, 0, result.stderr)
    self.assertIn("cumsum:     1 3 6 10 15", result.stdout)
    self.assertIn("cumsum^-1:  1 2 3 4 5", result.stdout)
    self.assertIn("xor_chain:  5 6 0 2 5", result.stdout)
    self.assertIn("odd_even:   20 10 40 30 60 50", result.stdout)
    self.assertIn("feistel4:   L=181 R=552", result.stdout)
    self.assertIn("feistel4^-1: L=5 R=7", result.stdout)

  def test_injective_bits_xor_gray_feistel(self) -> None:
    result = run_program(EXAMPLE_DIR / "injective_bits.ja")
    self.assertEqual(result.returncode, 0, result.stderr)
    # xor_key is an involution: applying the same key twice restores the input.
    self.assertIn("xor_key:    a=6 (k=10)", result.stdout)
    self.assertIn("xor_key x2: a=12", result.stdout)
    self.assertIn("xor_into:   x=240 y=15", result.stdout)
    # Gray(12) = 12 XOR 6 = 10; uncall recovers g=0.
    self.assertIn("gray_enc:   gx=12 g=10", result.stdout)
    self.assertIn("gray_dec:   gx=12 g=0", result.stdout)
    # Feistel round (L=5, R=7, K=3) -> (L=7, R=16); inverse restores it.
    self.assertIn("feistel:    L=7 R=16 (K=3)", result.stdout)
    self.assertIn("feistel^-1: L=5 R=7", result.stdout)


if __name__ == "__main__":
  unittest.main()
