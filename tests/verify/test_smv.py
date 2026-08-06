"""Tests for the SMV back-end (`jana_py.smv`).

The back-end compiles the *scalar fragment* of Janus to a nuXmv model whose
only reachable-error location stands for "a Janus runtime assertion failed".
Proving `pc != ERR` unreachable therefore proves that the program is a **total**
injection on the assumed domain.

These tests are pure unit tests over the generated model text; the tests that
actually invoke nuXmv live in `test_smv_nuxmv.py` and skip when it is absent.
"""

from __future__ import annotations

from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from jana_py import preprocess
from jana_py import parser_jana2014
from jana_py.smv import ERR_LOC, SmvUnsupported, compile_to_smv


def build(src: str, **kw) -> str:
  """Compile, defaulting to the relational shape the assertions below inspect."""
  kw.setdefault("style", "trans")
  pt = preprocess.preprocess_text("<test>", src, None, "jana2014")
  program = parser_jana2014.parse_program("<test>", pt.text, pt.line_origins)
  return compile_to_smv(program, **kw)


class ShapeTests(unittest.TestCase):
  def test_skip_program_is_well_formed(self):
    model = build("procedure main()\n    skip\n")
    self.assertIn("MODULE main", model)
    self.assertIn("pc : ", model)
    self.assertIn(f"INVARSPEC pc != {ERR_LOC}", model)

  def test_declared_variables_become_smv_integers(self):
    model = build("procedure main()\n    int x\n    x += 1\n")
    self.assertIn("x : integer;", model)

  def test_init_zero_pins_the_store(self):
    model = build("procedure main()\n    int x\n    x += 1\n", init="zero")
    self.assertIn("x = 0", model)

  def test_init_any_leaves_the_store_free(self):
    model = build("procedure main()\n    int x\n    x += 1\n", init="any")
    self.assertNotIn("x = 0", model)

  def test_assume_is_emitted(self):
    model = build("procedure main()\n    int x\n    x += 1\n",
                  init="any", assume="x >= 0")
    self.assertIn("x >= 0", model)


class ErrorBranchTests(unittest.TestCase):
  """Every Janus runtime assertion must produce a transition into ERR."""

  def test_assert_has_an_error_branch(self):
    model = build("procedure main()\n    assert(0=1)\n")
    self.assertIn(f"next(pc) = {ERR_LOC}", model)

  def test_if_exit_condition_has_an_error_branch(self):
    model = build("procedure main()\n    int x\n"
                  "    if x = 1 then\n        skip\n    fi x = 0\n")
    self.assertIn(f"next(pc) = {ERR_LOC}", model)

  def test_loop_entry_condition_has_an_error_branch(self):
    model = build("procedure main()\n    int x\n"
                  "    from x = 1\n    until x = 0\n")
    self.assertIn(f"next(pc) = {ERR_LOC}", model)

  def test_delocal_mismatch_has_an_error_branch(self):
    model = build("procedure main()\n"
                  "    local   int x = 0\n    skip\n    delocal int x = 1\n")
    self.assertIn(f"next(pc) = {ERR_LOC}", model)

  def test_division_by_zero_has_an_error_branch(self):
    model = build("procedure main()\n    int x\n    x += 5 / 0\n")
    self.assertIn(f"next(pc) = {ERR_LOC}", model)

  def test_a_program_without_assertions_has_no_error_branch(self):
    model = build("procedure main()\n    int x\n    x += 1\n")
    self.assertNotIn(f"next(pc) = {ERR_LOC}", model)


class FloorDivisionTests(unittest.TestCase):
  """nuXmv's integer `/` truncates toward zero; Janus (like Python) floors.

  A naive translation is therefore *unsound* on negative operands, so every
  division site must be emitted through the floor-division macro.
  """

  def test_division_emits_a_floor_correction(self):
    model = build("procedure main()\n    int x\n    int y\n    x += y / 3\n")
    self.assertIn("DEFINE", model)
    self.assertIn("- 1", model)  # the floor correction term

  def test_modulo_is_derived_from_floor_division(self):
    model = build("procedure main()\n    int x\n    int y\n    x += y % 3\n")
    self.assertIn("DEFINE", model)


class InitTests(unittest.TestCase):
  """`--init zero` means the store PyJanus starts from — locals included.

  Locals used to get no `init` at all, leaving them free: the "zero store" was
  not a single state, and every undecided program in the corpus carried free
  locals (32 of them in `injective_gcd`).  Over-approximating like that is a
  latent false-alarm source, whatever it does to the decision rate.
  """

  SRC = ("procedure main()\n    int x\n"
         "    local   int t = 1\n    x += t\n    delocal int t = 1\n")

  def test_a_local_is_pinned_under_init_zero(self):
    self.assertIn("init(t) := 0;", build(self.SRC, init="zero", style="assign"))

  def test_a_local_stays_free_under_init_any(self):
    self.assertNotIn("init(t) :=", build(self.SRC, init="any", style="assign"))

  def test_the_relational_form_pins_it_too(self):
    self.assertIn("t = 0", build(self.SRC, init="zero", style="trans"))


class FragmentTests(unittest.TestCase):
  """Everything outside the fragment must be refused, never mistranslated."""

  def _refuses(self, src: str):
    with self.assertRaises(SmvUnsupported):
      build(src)

  def test_an_argument_that_is_not_a_plain_variable_is_refused(self):
    # Arrays now pass by reference through inlining, which supplies the length
    # (`tests/verify/test_smv_array.py`).  What the expansion cannot resolve is
    # an argument that is not simply a name.
    self._refuses("procedure f(int a[])\n    a[0] += 1\n\n"
                  "procedure main()\n    int a[4]\n    call f(a[0])\n")

  def test_a_swap_between_a_scalar_and_a_cell_is_refused(self):
    # Cells swap with cells (`tests/verify/test_smv_array.py`); mixing a scalar
    # with an array cell is not something the expansion resolves.
    self._refuses("procedure main()\n    int a[4]\n    int x\n    a[0] <=> x\n")

  def test_a_rank_that_disagrees_with_the_declaration_is_refused(self):
    # Rank > 1 is translated (`tests/verify/test_smv_multidim.py`); indexing it
    # with the wrong number of subscripts is not, because the offset would be
    # meaningless rather than merely unknown.
    self._refuses("procedure main()\n    int a[2][2]\n    a[0] += 1\n")

  def test_stacks_are_refused(self):
    self._refuses("procedure main()\n    int x\n    stack s\n    push(x, s)\n")

  def test_bitwise_xor_assignment_is_refused(self):
    self._refuses("procedure main()\n    int x\n    x ^= 1\n")

  def test_bitwise_operators_are_refused(self):
    self._refuses("procedure main()\n    int x\n    int y\n    x += y & 1\n")

  def test_exponentiation_is_refused(self):
    self._refuses("procedure main()\n    int x\n    int y\n    x += y ** 2\n")

  def test_mixing_boolean_and_integer_sorts_is_refused(self):
    # `x += (y > 0)` is legal Janus but the two-sorted translation refuses it
    # rather than guessing; this mirrors the `wf` discipline of RevLowerExpr.v.
    self._refuses("procedure main()\n    int x\n    int y\n    x += (y > 0)\n")

  def test_printf_is_ignored_not_refused(self):
    model = build('procedure main()\n    int x\n    x += 1\n'
                  '    printf("%d\\n", x)\n')
    self.assertIn("MODULE main", model)


class StyleTests(unittest.TestCase):
  """Both output shapes describe the same system; `assign` is much smaller.

  The functional form replaces one `next(v) = v` per variable per edge with a
  single `TRUE` default, which measured about 7x smaller on `fall_c.ja`.  It made
  no difference to what nuXmv could decide, but a smaller model is the better
  default for the array work to come.
  """

  SOURCE = ("procedure main()\n    int x\n"
            "    if x = 1 then\n        skip\n    fi x = 0\n")

  def test_assign_is_the_default(self):
    pt = preprocess.preprocess_text("<test>", self.SOURCE, None, "jana2014")
    program = parser_jana2014.parse_program("<test>", pt.text, pt.line_origins)
    self.assertIn("ASSIGN", compile_to_smv(program))

  def test_assign_form_keeps_the_error_branch(self):
    model = build(self.SOURCE, style="assign")
    self.assertIn(f": {ERR_LOC};", model)
    self.assertNotIn("TRANS", model)

  def test_assign_form_is_smaller(self):
    self.assertLess(len(build(self.SOURCE, style="assign")),
                    len(build(self.SOURCE, style="trans")))

  def test_an_unknown_style_is_rejected(self):
    with self.assertRaises(ValueError):
      build("procedure main()\n    skip\n", style="relational")


class RuntimeCheckTests(unittest.TestCase):
  """Janus checks aliasing and delocal names at *run time*, not statically.

  A naive translation of `x += x` is `next(x) = x + x`, which is not injective
  — the model would prove a non-reversible program safe.  Reaching such a
  statement is itself the error, so it becomes an unconditional edge to ERR;
  on an unreachable path it is correctly no error at all.
  """

  def test_self_referential_update_is_an_error(self):
    model = build("procedure main()\n    int x\n    x += x\n")
    self.assertIn(f"next(pc) = {ERR_LOC}", model)
    self.assertNotIn("next(x) = (x + x)", model)

  def test_aliasing_through_a_call_is_an_error(self):
    model = build("procedure bar(int a, int b)\n    a += b\n\n"
                  "procedure main()\n    int x\n    call bar(x, x)\n")
    self.assertIn(f"next(pc) = {ERR_LOC}", model)

  def test_mismatched_delocal_name_is_an_error(self):
    model = build("procedure main()\n"
                  "    local int foo = 0\n    local int bar = 0\n    skip\n"
                  "    delocal int foo = 0\n    delocal int bar = 0\n")
    self.assertIn(f"next(pc) = {ERR_LOC}", model)


class ProcedureTests(unittest.TestCase):
  def test_call_is_inlined(self):
    model = build("procedure inc(int a)\n    a += 1\n\n"
                  "procedure main()\n    int x\n    call inc(x)\n")
    self.assertIn("next(x) = (x + 1)", model)

  def test_uncall_is_inlined_inverted(self):
    model = build("procedure inc(int a)\n    a += 1\n\n"
                  "procedure main()\n    int x\n    uncall inc(x)\n")
    self.assertIn("next(x) = (x - 1)", model)

  def test_recursion_beyond_the_bound_reaches_the_bound_location(self):
    src = ("procedure down(int n)\n"
           "    if n = 0 then\n        skip\n    else\n"
           "        n -= 1\n        call down(n)\n        n += 1\n"
           "    fi n = 0\n\n"
           "procedure main()\n    int n\n    n += 3\n    call down(n)\n")
    model = build(src, max_depth=1)
    self.assertIn("BOUND", model)


if __name__ == "__main__":
  unittest.main()
