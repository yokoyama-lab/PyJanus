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

  def test_injective_cipher_sbox_feistel_with_key_schedule(self) -> None:
    result = run_program(EXAMPLE_DIR / "injective_cipher_sbox.ja")
    self.assertEqual(result.returncode, 0, result.stderr)
    # Master key 6 with constants (0, 5, 11, 14) gives round keys
    # (6, 3, 13, 8) under XOR-mixing.
    self.assertIn("round keys:  6 3 13 8", result.stdout)
    # Four Feistel rounds with the PRESENT S-box encrypt (5, 10) to (4, 8).
    self.assertIn("encrypt:     L=4 R=8", result.stdout)
    # uncall encrypt decrypts back to the plaintext.
    self.assertIn("decrypt:     L=5 R=10", result.stdout)
    # uncall key_schedule clears the derived round keys.
    self.assertIn("rk cleared:  0 0 0 0", result.stdout)

  def test_injective_ca_rule90_second_order(self) -> None:
    result = run_program(EXAMPLE_DIR / "injective_ca_rule90.ja")
    self.assertEqual(result.returncode, 0, result.stderr)
    # After 3 second-order Rule-90 steps from a single-cell impulse, the
    # newer slot (a) holds state[t=3], the older slot (b) holds state[t=2].
    self.assertIn("a (t=3):    01010101", result.stdout)
    self.assertIn("b (t=2):    00101010", result.stdout)
    # uncall runs time backwards and recovers the (zeros, impulse) pair.
    self.assertIn("a restored: 00000000", result.stdout)
    self.assertIn("b restored: 00001000", result.stdout)

  def test_injective_vm_stack_machine_roundtrip(self) -> None:
    result = run_program(EXAMPLE_DIR / "injective_vm.ja")
    self.assertEqual(result.returncode, 0, result.stderr)
    # Program [PUSH 5, PUSH 3, ADD, PUSH 10, SUB] yields stack <5, 8, 2>.
    self.assertIn("after run:    top=2 below=8", result.stdout)
    # uncall of the program runs every instruction backwards, emptying
    # the stack again.
    self.assertIn("after uncall: size=0", result.stdout)

  def test_injective_lehmer_perm_to_factorial_base(self) -> None:
    result = run_program(EXAMPLE_DIR / "injective_lehmer.ja")
    self.assertEqual(result.returncode, 0, result.stderr)
    # Lehmer left-rank code of [2, 0, 3, 1].
    self.assertIn("code:     0 0 2 1", result.stdout)
    # Factorial base: 0*0! + 0*1! + 2*2! + 1*3! = 4 + 6 = 10.
    self.assertIn("integer:  10", result.stdout)
    # uncall of the chain restores the permutation and clears the integer.
    self.assertIn("restored: 2 0 3 1 (int=0)", result.stdout)

  def test_injective_partition_reversible_lomuto(self) -> None:
    result = run_program(EXAMPLE_DIR / "injective_partition.ja")
    self.assertEqual(result.returncode, 0, result.stderr)
    # pivot = a[7] = 6; five elements are smaller, so the pivot lands at index 5.
    self.assertIn("part a:    3 2 5 1 4 6 7 8  (pivot@5)", result.stdout)
    # one decision bit per scanned position 0..6 (1 = element went left).
    self.assertIn("flags a:   1011110", result.stdout)
    # uncall scatters the elements back and clears p.
    self.assertIn("uncall a:  3 8 2 5 1 4 7 6  (p=0)", result.stdout)
    # already-sorted, pivot is the max: nothing moves, final pivot swap suppressed.
    self.assertIn("part b:    1 2 3 4  (pivot@3)  flags=111", result.stdout)

  def test_injective_arith_coding_rans_roundtrip(self) -> None:
    result = run_program(EXAMPLE_DIR / "injective_arith_coding.ja")
    self.assertEqual(result.returncode, 0, result.stderr)
    # rANS folds [1,0,1,0] into x = 25 under the f0=3,f1=1 model, consuming the
    # message (every symbol ends 0) and leaving the q,r ancillas clean.
    self.assertIn("encoded:   x=25   msg=0000  (q=0 r=0)", result.stdout)
    # uncall is the decoder: it reads the symbols back and clears x to 0.
    self.assertIn("decoded:   msg=1010   x=0  (q=0 r=0)", result.stdout)

  def test_injective_mini_cipher_three_round_feistel(self) -> None:
    result = run_program(EXAMPLE_DIR / "injective_mini_cipher.ja")
    self.assertEqual(result.returncode, 0, result.stderr)
    # Three rounds of additive Feistel over Z/256 with round keys
    # (200, 150, 91) map (100, 42) -> (250, 231). Round 0 triggers a
    # modular overflow, recorded as logs[0] = 1.
    self.assertIn("encrypt:  L=250 R=231  logs=100", result.stdout)
    # uncall reverses the cipher and clears every log bit.
    self.assertIn("decrypt:  L=100 R=42  logs=000", result.stdout)

  def test_injective_sort_network_with_swap_log(self) -> None:
    result = run_program(EXAMPLE_DIR / "injective_sort_network.ja")
    self.assertEqual(result.returncode, 0, result.stderr)
    # Fully reversed input: all five comparators swap.
    self.assertIn("sort4 a:   1 2 3 4  log=11111", result.stdout)
    # uncall replays the log backwards to restore the original order.
    self.assertIn("uncall a:  4 2 3 1  log=00000", result.stdout)
    # Already-sorted input: no comparator swaps.
    self.assertIn("sort4 b:   1 2 3 4  log=00000", result.stdout)

  def test_injective_gcd_reversible_euclidean(self) -> None:
    result = run_program(EXAMPLE_DIR / "injective_gcd.ja")
    self.assertEqual(result.returncode, 0, result.stderr)
    self.assertIn("gcd(12,18): a=12 b=18 g=6", result.stdout)
    # uncall the Bennett-wrapped GCD restores g=0 with a, b untouched.
    self.assertIn("uncalled:   a=12 b=18 g=0", result.stdout)
    self.assertIn("gcd(21,14): a=21 b=14 g=7", result.stdout)
    # Edge case: gcd(0, n) = n (the loop runs zero iterations).
    self.assertIn("gcd(0,9):   a=0 b=9 g=9", result.stdout)

  def test_injective_bennett_divmod_garbage_free(self) -> None:
    result = run_program(EXAMPLE_DIR / "injective_bennett.ja")
    self.assertEqual(result.returncode, 0, result.stderr)
    # Forward: divmod_clean preserves x and d, fills q and r.
    self.assertIn("divmod(17,5): x=17 d=5 q=3 r=2", result.stdout)
    # uncall clears q and r without disturbing x or d.
    self.assertIn("uncalled:     x=17 d=5 q=0 r=0", result.stdout)
    # Edge case: x < d gives q=0, r=x.
    self.assertIn("divmod(3,5):  x=3 q=0 r=3", result.stdout)

  def test_injective_arithmetic_factorial_ipow_horner(self) -> None:
    result = run_program(EXAMPLE_DIR / "injective_arithmetic.ja")
    self.assertEqual(result.returncode, 0, result.stderr)
    self.assertIn("factorial:  5! = 120", result.stdout)
    self.assertIn("ipow:       2^10 = 1024", result.stdout)
    self.assertIn("horner:     p(4) = 57", result.stdout)
    # Reversibility: uncall of each procedure clears the result.
    self.assertIn("cleared:    fact=0 pow=0 y=0", result.stdout)

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
