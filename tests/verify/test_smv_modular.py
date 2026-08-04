"""The checker must refuse the modular modes rather than model them wrongly.

`--smv` compiles the *unbounded-integer* semantics.  `-m BITS` and `-p PRIME`
change what the interpreter computes — every value wraps — so a model built
without them is about a different program, and `INVARSPEC pc != ERR` proved of
it says nothing about the program that runs.  This was live:

    procedure main()
        int x
        x += 100
        x += 100
        assert(x = 200)

`pyjanus -m 8` fails (100 + 100 wraps to -56), while the model emitted for the
same invocation declares `x : integer` and nuXmv proves it safe.  It is the same
class of defect as the missing swap aliasing check, except that it needs no
unusual program: it applies to every program run in a modular mode.

Refusing is the right fix *now* whichever way the design question goes.  Adding
a modular encoding later is a real option — `coq/RevSMod.v` and
`coq/RevExtSMod.v` are its verified target — but it cannot reuse the current
obligations: in a residue ring the side condition for `*=` / `/=` is that the
factor be a **unit**, not that it be nonzero (`runtime.py` raises
"Multiplication by {operand} is not invertible modulo {modulus}").  Until that
is done, refusing is the only honest answer.

The refusal lives in `compile_to_smv`, not only in the CLI, so a library caller
(`tools/verify_corpus.py`, these tests) cannot get a wrong model either.
"""

from __future__ import annotations

from pathlib import Path
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from jana_py import nuxmv
from jana_py import parser_jana2014
from jana_py import preprocess
from jana_py.smv import SmvUnsupported
from jana_py.smv import compile_to_smv

BINARY = nuxmv.find_nuxmv()

#: Fails under `-m 8` (wraps to -56) and succeeds over the unbounded integers.
WRAPPING = ("procedure main()\n"
            "    int x\n"
            "    x += 100\n"
            "    x += 100\n"
            "    assert(x = 200)\n")


def program_of(src: str):
  pt = preprocess.preprocess_text("<test>", src, None, "jana2014")
  return parser_jana2014.parse_program("<test>", pt.text, pt.line_origins)


def run_cli(*extra: str, src: str = WRAPPING) -> subprocess.CompletedProcess:
  return subprocess.run(
      [sys.executable, "-m", "jana_py.cli", "--std", "jana2014", *extra, "-"],
      input=src, capture_output=True, text=True, cwd=ROOT)


class ReferenceBehaviourTests(unittest.TestCase):
  """The divergence the refusal exists for."""

  def test_the_interpreter_fails_under_m_bits(self):
    self.assertNotEqual(run_cli("-m", "8", "-s").returncode, 0)

  def test_the_interpreter_succeeds_without_a_modulus(self):
    self.assertEqual(run_cli("-s").returncode, 0)


class RefusalTests(unittest.TestCase):
  """`compile_to_smv` refuses; it does not emit an unbounded model."""

  def test_modular_bits_are_refused(self):
    with self.assertRaises(SmvUnsupported):
      compile_to_smv(program_of(WRAPPING), init="zero", mod_bits=8)

  def test_modular_prime_is_refused(self):
    with self.assertRaises(SmvUnsupported):
      compile_to_smv(program_of(WRAPPING), init="zero", mod_prime=7)

  def test_no_modulus_still_compiles(self):
    model = compile_to_smv(program_of(WRAPPING), init="zero")
    self.assertIn("INVARSPEC", model)

  def test_an_explicit_none_is_not_a_modulus(self):
    # `cli.py` passes the parsed options straight through, and they are `None`
    # when the flags are absent.
    model = compile_to_smv(program_of(WRAPPING), init="zero",
                           mod_bits=None, mod_prime=None)
    self.assertIn("INVARSPEC", model)


class CliTests(unittest.TestCase):
  """...and the CLI reports it instead of printing a model."""

  def test_smv_with_m_is_rejected(self):
    proc = run_cli("--smv", "-m", "8")
    self.assertNotEqual(proc.returncode, 0)
    self.assertNotIn("MODULE main", proc.stdout)
    self.assertIn("-m", proc.stdout + proc.stderr)

  def test_smv_with_p_is_rejected(self):
    proc = run_cli("--smv", "-p", "7")
    self.assertNotEqual(proc.returncode, 0)
    self.assertNotIn("MODULE main", proc.stdout)

  def test_smv_without_a_modulus_still_prints_a_model(self):
    proc = run_cli("--smv")
    self.assertEqual(proc.returncode, 0)
    self.assertIn("MODULE main", proc.stdout)


@unittest.skipIf(BINARY is None, "nuXmv not installed")
class WhyItMattersTests(unittest.TestCase):
  """The unbounded model really does prove the program that `-m 8` fails.

  This is the demonstration, kept as a test so the justification for the refusal
  cannot quietly stop being true.
  """

  def test_the_unbounded_model_proves_what_the_modular_run_refutes(self):
    self.assertNotEqual(run_cli("-m", "8", "-s").returncode, 0)
    result = nuxmv.check(compile_to_smv(program_of(WRAPPING), init="zero"),
                         binary=BINARY)
    self.assertEqual(result.status, "proved", result.output[-2000:])


if __name__ == "__main__":
  unittest.main()
