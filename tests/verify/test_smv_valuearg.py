"""Arguments that are not l-values — `call shift(a, 5)`, `call f(n - 1, r)`.

The queue item that asked for this described them as read-only constants bound
through `ConstantParamProxy`, with an assignment inside the callee being the
error.  **That is not what PyJanus does.**  `ConstantParamProxy` is for a
parameter declared `const`; a non-l-value *argument* is a **value argument**,
and `runtime._bind_args` says what it means:

    call f(n-1, r)  desugars to  local t = n-1; call f(t, r); delocal t = n-1

So the cell is writable, and the obligation is at the *end*: the argument
expression must read back the bound value when the call returns.  Writing to it
is fine as long as the callee puts it back — probed against the interpreter
below, because getting this backwards would refuse programs that run.

Two consequences the encoding has to get right:

* the exit expression is re-evaluated **after** the body, in the *caller's*
  environment, so a callee that changes `m` through another parameter changes
  what `m + 1` means on return;
* this is exactly `local`/`delocal`, so it reuses that path rather than adding
  a notion of read-only binding.
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


def model_of(src: str, **kw) -> str:
  pt = preprocess.preprocess_text("<test>", src, None, "jana2014")
  program = parser_jana2014.parse_program("<test>", pt.text, pt.line_origins)
  return compile_to_smv(program, **kw)


def reaches_err(model: str) -> bool:
  return ": 0;" in model.split("next(pc) := case")[1].split("esac;")[0]


def interpreter_fails(src: str) -> bool:
  proc = subprocess.run([sys.executable, "-m", "jana_py.cli", "--std", "jana2014", "-s", "-"],
                        input=src, capture_output=True, text=True, cwd=ROOT)
  return proc.returncode != 0


RESTORED = ("procedure bump(int x)\n    x += 1\n    x -= 1\n\n"
            "procedure main()\n    int y\n    y += 1\n    call bump(5)\n")
NOT_RESTORED = ("procedure bump(int x)\n    x += 1\n\n"
                "procedure main()\n    int y\n    call bump(5)\n")
EXPRESSION = ("procedure add(int x, int r)\n    r += x\n\n"
              "procedure main()\n    int n\n    int r\n    n += 3\n"
              "    call add(n + 1, r)\n")
#: The callee moves `m`, so `m + 1` means something else on return.
MOVED = ("procedure f(int x, int m)\n    m += 1\n\n"
         "procedure main()\n    int m\n    call f(m + 1, m)\n")
COMPENSATED = ("procedure f(int x, int m)\n    m += 1\n    x += 1\n\n"
               "procedure main()\n    int m\n    call f(m + 1, m)\n")
UNCALL = ("procedure f(int x, int r)\n    r += x\n\n"
          "procedure main()\n    int r\n    r += 7\n    uncall f(7, r)\n")


class InterpreterSemanticsTests(unittest.TestCase):
  """What the model has to match.  Probed, because the queue item had it wrong."""

  def test_a_value_argument_may_be_written_and_put_back(self):
    self.assertFalse(interpreter_fails(RESTORED))

  def test_leaving_it_changed_is_the_error(self):
    self.assertTrue(interpreter_fails(NOT_RESTORED))

  def test_the_exit_expression_is_re_evaluated_after_the_body(self):
    self.assertTrue(interpreter_fails(MOVED))
    self.assertFalse(interpreter_fails(COMPENSATED))


class EncodingTests(unittest.TestCase):
  def test_the_argument_is_bound_and_checked_on_return(self):
    # Both programs get the same shape — a binding and an exit obligation.
    # The obligation is a *condition*, not a refusal, and the edge to ERR is
    # emitted either way (nothing constant-folds it); which of the two can
    # actually reach ERR is nuXmv's job, fixed in `AgreementTests`.
    for src in (RESTORED, NOT_RESTORED):
      model = model_of(src, init="zero")
      self.assertTrue(reaches_err(model))
      # The formal's accumulated term, compared back to the argument.
      self.assertIn(") = 5)", model)

  def test_the_obligation_names_the_exit_value_not_the_entry_value(self):
    # `f(m + 1, m)` with the callee moving `m`: the check must mention `m`'s
    # value *after* the body, so the term is the updated one, not `m` itself.
    model = model_of(MOVED, init="zero")
    self.assertIn("((m + 1) + 1)", model)

  def test_an_expression_argument_is_bound_by_value(self):
    model = model_of(EXPRESSION, init="zero")
    self.assertIn("((n + 3) + 1)", model)

  def test_a_cell_argument_is_still_refused(self):
    src = ("procedure f(int x)\n    x += 1\n    x -= 1\n\n"
           "procedure main()\n    int a[2]\n    call f(a[0])\n")
    with self.assertRaises(SmvUnsupported):
      model_of(src, init="zero")


class CorpusTests(unittest.TestCase):
  NOW_IN = ("structs_param_c.ja", "structs_flat_param_c.ja")

  def test_they_compile(self):
    for name in self.NOW_IN:
      with self.subTest(name):
        path = ROOT / "tests/jana2014/fixtures/examples" / name
        self.assertIn("INVARSPEC", model_of(path.read_text(encoding="utf-8"), init="zero"))


@unittest.skipIf(BINARY is None, "nuXmv not installed")
class AgreementTests(unittest.TestCase):
  def test_the_model_checker_agrees_with_the_interpreter(self):
    for name, src in (("restored", RESTORED), ("not-restored", NOT_RESTORED),
                      ("expression", EXPRESSION), ("moved", MOVED),
                      ("compensated", COMPENSATED), ("uncall", UNCALL)):
      with self.subTest(name):
        fails = interpreter_fails(src)
        result = nuxmv.check(model_of(src, init="zero"), binary=BINARY)
        self.assertEqual(result.status, "refuted" if fails else "proved",
                         result.output[-2000:])


if __name__ == "__main__":
  unittest.main()
