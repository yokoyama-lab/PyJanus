"""Pin `smv.py`'s aliasing decision to the one proved exact in Rocq.

`coq/RevSmvAlias.v` proves that the checker's per-statement test

    alias_ok env (TAsn x _ e) = negb (aoccurs env (env x) e)
    alias_ok env (TSwap x y) = negb (Nat.eqb (env x) (env y))

is *exactly* the reference semantics' side condition, in both directions:

    step_alias_ok        : sexec (rn_stmt env s) g h -> alias_ok env s = true
    alias_flagged_no_step: alias_ok env s = false -> ~ sexec (rn_stmt env s) g h

The first is what a `proved` verdict rests on (no aliasing violation is modelled
as an ordinary update); the second is what a `refuted` verdict rests on (a
flagged statement really cannot run).  These tests say the *compiler* implements
that decision: for each program, whether the emitted model can reach ERR must
agree with whether PyJanus rejects the program.

Two of the cases below are regressions for gaps the mechanization found:

* `self_swap` / `swap_through_params` — the swap case had no aliasing check at
  all, so `x <=> x` was symbolically executed as a simultaneous exchange, which
  for one variable is the identity.  The model had no ERR edge while PyJanus
  raises: a proof of `INVARSPEC pc != ERR` about a program that fails.
* `harmless_double_binding` — the call site rejected *any* two parameters bound
  to the same variable, even when no statement in the body ever brings them
  together.  PyJanus runs such a program, so that was a false alarm.

`test_smv_expr.py` does the same job for the floor-division macro.
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
from jana_py.smv import compile_to_smv

BINARY = nuxmv.find_nuxmv()

#: Programs PyJanus rejects at run time because of aliasing.
ALIASING = {
    # `x += x` — the statement that motivated the whole check.
    "direct": "procedure main()\n    int x\n    x += 5\n    x += x\n",
    # the same, arising only after inlining resolves the parameters.
    "through_params": ("procedure bar(int a, int b)\n    a += b\n\n"
                       "procedure main()\n    int x\n    x += 5\n    call bar(x, x)\n"),
    # two levels of resolution — `alias-1.ja`'s shape.
    "two_levels": ("procedure foo(int p, int q)\n    call bar(p, q)\n\n"
                   "procedure bar(int a, int b)\n    a += b\n\n"
                   "procedure main()\n    int x\n    x += 5\n    call foo(x, x)\n"),
    # `x <=> x`: the identity as a relation, an error in Janus.
    "self_swap": "procedure main()\n    int x\n    x += 5\n    x <=> x\n",
    # ...and through parameters, which is how it actually arises.
    "swap_through_params": ("procedure swapit(int a, int b)\n    a <=> b\n\n"
                            "procedure main()\n    int x\n    x += 5\n"
                            "    call swapit(x, x)\n"),
    # uncall inverts the body, and the alias survives the inversion.
    "uncalled_alias": ("procedure bar(int a, int b)\n    a += b\n\n"
                       "procedure main()\n    int x\n    x += 5\n    uncall bar(x, x)\n"),
}

#: Programs PyJanus accepts, which must therefore *not* reach ERR.
CLEAN = {
    "distinct_add": "procedure main()\n    int x\n    int y\n    y += 1\n    x += y\n",
    "distinct_swap": "procedure main()\n    int x\n    int y\n    x += 1\n    x <=> y\n",
    # Two formals bound to one variable is not itself an error: PyJanus checks
    # each statement as it reaches it, and this body never brings them together.
    "harmless_double_binding": ("procedure noalias(int a, int b)\n    a += 1\n\n"
                                "procedure main()\n    int x\n    call noalias(x, x)\n"),
    # The target occurs in an *earlier* statement's pending expression, which is
    # not aliasing — the check is on the source expression, before substitution.
    "pending_is_not_aliasing": ("procedure main()\n    int x\n    int y\n"
                                "    x += 1\n    x += y\n    y += x\n"),
}


def model_of(src: str, **kw) -> str:
  pt = preprocess.preprocess_text("<test>", src, None, "jana2014")
  program = parser_jana2014.parse_program("<test>", pt.text, pt.line_origins)
  return compile_to_smv(program, **kw)


def has_err_edge(model: str) -> bool:
  """Does the emitted model have any transition into ERR (`pc = 0`)?

  In the functional form ERR appears as a `: 0;` branch of `next(pc)`; the
  absorbing self-loop at ERR is only emitted in the relational form, so a model
  that never fails mentions location 0 in the comment and the INVARSPEC alone.
  """
  in_pc = False
  for line in model.splitlines():
    if line.strip().startswith("next(pc) :="):
      in_pc = True
      continue
    if in_pc:
      if line.strip() == "esac;":
        return False
      if line.strip().endswith(": 0;"):
        return True
  return False


def interpreter_fails(src: str) -> bool:
  """True when PyJanus itself reports a runtime error on the zero store."""
  proc = subprocess.run([sys.executable, "-m", "jana_py.cli", "--std", "jana2014", "-s", "-"],
                        input=src, capture_output=True, text=True, cwd=ROOT)
  return proc.returncode != 0


class ReferenceBehaviourTests(unittest.TestCase):
  """First: the reference these tests compare against is what we think it is."""

  def test_the_aliasing_programs_are_rejected_by_pyjanus(self):
    for name, src in ALIASING.items():
      with self.subTest(name):
        self.assertTrue(interpreter_fails(src))

  def test_the_clean_programs_are_accepted_by_pyjanus(self):
    for name, src in CLEAN.items():
      with self.subTest(name):
        self.assertFalse(interpreter_fails(src))


class EncodingTests(unittest.TestCase):
  """The emitted model flags a statement exactly when the source cannot run it.

  This is `alias_check_is_exact` at the level of the compiler: `has_err_edge`
  stands for "the checker considers this reachable statement a failure".
  """

  def test_aliasing_programs_get_an_err_edge(self):
    for name, src in ALIASING.items():
      with self.subTest(name):
        self.assertTrue(has_err_edge(model_of(src, init="zero")),
                        f"{name}: no ERR edge, so the model would be proved safe")

  def test_clean_programs_get_no_err_edge(self):
    for name, src in CLEAN.items():
      with self.subTest(name):
        self.assertFalse(has_err_edge(model_of(src, init="zero")),
                         f"{name}: a spurious ERR edge would be a false alarm")

  def test_a_self_swap_is_not_modelled_as_the_identity(self):
    # The specific gap: symbolic execution of `x <=> x` exchanges one pending
    # entry with itself.  Without the check the model has no ERR edge at all.
    model = model_of(ALIASING["self_swap"], init="zero")
    self.assertTrue(has_err_edge(model))

  def test_a_double_binding_alone_is_not_an_error(self):
    # The other gap, in the other direction: this program runs, so the model
    # must let it run.
    model = model_of(CLEAN["harmless_double_binding"], init="zero")
    self.assertFalse(has_err_edge(model))


@unittest.skipIf(BINARY is None, "nuXmv not installed")
class AgreementTests(unittest.TestCase):
  """...and nuXmv decides the models the way the interpreter behaves."""

  def test_aliasing_programs_are_refuted(self):
    for name, src in ALIASING.items():
      with self.subTest(name):
        result = nuxmv.check(model_of(src, init="zero"), binary=BINARY)
        self.assertEqual(result.status, "refuted", result.output[-2000:])

  def test_clean_programs_are_proved(self):
    for name, src in CLEAN.items():
      with self.subTest(name):
        result = nuxmv.check(model_of(src, init="zero"), binary=BINARY)
        self.assertEqual(result.status, "proved", result.output[-2000:])


if __name__ == "__main__":
  unittest.main()
