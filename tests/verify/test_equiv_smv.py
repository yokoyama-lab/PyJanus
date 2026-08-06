"""Symbolic program equivalence: decide `P; Q†` against the identity.

`tests/*/test_equiv.py` covers the *testing* checker in `jana_py.equiv`, which
runs both programs on a box of inputs.  These tests cover the *proving* one:
the model must be shaped so that nuXmv decides equivalence over unbounded
integers, and the refusals must fire rather than emit a spec that constrains
nothing.  The nuXmv half is skipped when the binary is absent.
"""

from __future__ import annotations

import unittest

from jana_py import nuxmv
from jana_py import parser_jana2014
from jana_py import preprocess
from jana_py.equiv_smv import (
    _FROZEN_SUFFIX,
    check_equivalence_smv,
    compile_equivalence_to_smv,
    compose_with_inverse,
)
from jana_py.format import format_program
from jana_py.smv import SmvUnsupported

BINARY = nuxmv.find_nuxmv()

HEAD = "procedure main()\n    int x\n    int y\n"


def prog(src: str):
  pt = preprocess.preprocess_text("<test>", src, None, "jana2014")
  return parser_jana2014.parse_program("<test>", pt.text, pt.line_origins)


class CompositionTests(unittest.TestCase):
  """`P; Q†` must be built, not approximated."""

  def test_the_body_is_p_then_q_inverted(self):
    a = prog(HEAD + "    x += y\n")
    b = prog(HEAD + "    x += 1\n    y -= 2\n")
    composed = compose_with_inverse(a, b)
    text = format_program(composed)
    # Q = (x += 1; y -= 2), so Q† = (y += 2; x -= 1), appended after P.
    self.assertIn("x += y", text)
    self.assertLess(text.index("x += y"), text.index("y += 2"))
    self.assertLess(text.index("y += 2"), text.index("x -= 1"))

  def test_main_initializers_are_dropped(self):
    """A declared initializer would override `init=any` and fix the input."""
    a = prog("procedure main()\n    int x = 5\n    x += 1\n")
    b = prog("procedure main()\n    int x = 5\n    x += 1\n")
    composed = compose_with_inverse(a, b)
    self.assertTrue(all(v.init_expr is None for v in composed.main.vdecls))

  def test_a_different_interface_is_refused(self):
    a = prog(HEAD + "    x += y\n")
    b = prog("procedure main()\n    int x\n    int z\n    x += z\n")
    with self.assertRaises(SmvUnsupported) as caught:
      compose_with_inverse(a, b)
    self.assertIn("different main variables", str(caught.exception))

  def test_a_clashing_procedure_is_refused(self):
    a = prog("procedure p(int a)\n    a += 1\n"
             "procedure main()\n    int x\n    call p(x)\n")
    b = prog("procedure p(int a)\n    a += 2\n"
             "procedure main()\n    int x\n    call p(x)\n")
    with self.assertRaises(SmvUnsupported) as caught:
      compose_with_inverse(a, b)
    self.assertIn("different", str(caught.exception))

  def test_a_clashing_procedure_is_refused_even_at_a_different_line(self):
    """The two programs are different files, so the clash is normally off-line.

    Keying the merge on `Proc.procname` (an `Ident` carrying a `SourcePos`)
    instead of on its string made this case slip through: the names compared
    unequal and both definitions were inlined into one model.
    """
    a = prog("procedure p(int a)\n    a += 1\n"
             "procedure main()\n    int x\n    call p(x)\n")
    b = prog("\n\nprocedure p(int a)\n    a += 2\n"
             "procedure main()\n    int x\n    call p(x)\n")
    with self.assertRaises(SmvUnsupported):
      compose_with_inverse(a, b)

  def test_an_identical_procedure_is_merged_once(self):
    src_proc = "procedure p(int a)\n    a += 1\n"
    a = prog(src_proc + "procedure main()\n    int x\n    call p(x)\n")
    b = prog(src_proc + "procedure main()\n    int x\n    call p(x)\n")
    composed = compose_with_inverse(a, b)
    self.assertEqual([p.procname.name for p in composed.procs], ["p"])


class ModelShapeTests(unittest.TestCase):
  """The emitted model must actually constrain the interface at the exit."""

  def test_frozen_copies_and_identity_spec_are_emitted(self):
    a = prog(HEAD + "    x += y\n")
    b = prog(HEAD + "    x += y\n")
    built = compile_equivalence_to_smv(a, b)
    self.assertEqual(built.compared, ("x", "y"))
    self.assertIn("FROZENVAR", built.model)
    self.assertIn(f"x{_FROZEN_SUFFIX} : integer;", built.model)
    self.assertIn(f"INIT\n  x{_FROZEN_SUFFIX} = x", built.model)
    self.assertIn(f"x = x{_FROZEN_SUFFIX}", built.identity_prop)
    # The totality property of the underlying checker must survive.
    self.assertIn("INVARSPEC pc != 0", built.model)

  def test_declarations_precede_the_specs(self):
    """nuXmv parses in order; a FROZENVAR after an INVARSPEC is a parse error."""
    a = prog(HEAD + "    x += y\n")
    built = compile_equivalence_to_smv(a, a)
    self.assertLess(built.model.index("FROZENVAR"), built.model.index("INVARSPEC"))

  def test_equivalence_is_only_asked_over_every_store(self):
    a = prog(HEAD + "    x += y\n")
    with self.assertRaises(ValueError):
      compile_equivalence_to_smv(a, a, init="zero")

  def test_a_renamed_interface_variable_is_refused(self):
    """`smv.py` renames names nuXmv reserves; the spec must not silently drop them.

    Without this refusal the identity property would compare a variable that
    does not exist in the model, and nuXmv would prove a weaker statement.
    """
    src = "procedure main()\n    int K\n    K += 1\n"
    a = prog(src)
    with self.assertRaises(SmvUnsupported) as caught:
      compile_equivalence_to_smv(a, a)
    self.assertIn("does not track the renaming", str(caught.exception))

  def test_ancillas_are_not_compared(self):
    """A `local` is restored by `delocal`, not by returning to its entry value."""
    src = (HEAD + "    local int t = 0\n    t += x\n    x += t\n"
                  "    x -= t\n    t -= x\n    delocal int t = 0\n")
    built = compile_equivalence_to_smv(prog(src), prog(src))
    self.assertEqual(built.compared, ("x", "y"))
    self.assertNotIn(f"t{_FROZEN_SUFFIX}", built.model)


@unittest.skipIf(BINARY is None, "nuXmv not installed")
class DecisionTests(unittest.TestCase):
  """What IC3 actually decides, and the three outcomes kept apart."""

  def check(self, src_a: str, src_b: str, **kw):
    return check_equivalence_smv(prog(src_a), prog(src_b), timeout=180, **kw)

  def test_an_algebraic_rewrite_is_proved_equivalent(self):
    v = self.check(HEAD + "    x += y\n",
                   HEAD + "    x += y + 1\n    x -= 1\n")
    self.assertEqual(v.status, "equivalent")
    self.assertEqual((v.identity, v.totality), ("proved", "proved"))

  def test_a_wrong_rewrite_is_refuted_with_a_counterexample(self):
    v = self.check(HEAD + "    x += y\n", HEAD + "    x += y + 1\n")
    self.assertEqual(v.status, "different")
    self.assertEqual(v.identity, "refuted")
    self.assertNotIn(f"x{_FROZEN_SUFFIX}", v.counterexample)

  def test_agreeing_programs_with_different_domains_are_partial(self):
    """`P` asserts and `Q` does not: the completing runs agree, the domains do not.

    Collapsing this into "different" would be wrong — the programs compute the
    same function wherever both are defined.
    """
    v = self.check(HEAD + "    assert(x >= 0)\n    x += y\n",
                   HEAD + "    x += y\n")
    self.assertEqual(v.status, "partial")
    self.assertEqual((v.identity, v.totality), ("proved", "refuted"))

  def test_a_loop_folded_to_a_closed_form_needs_its_precondition(self):
    """The headline case: an unbounded-integer proof that a loop equals `x += 3`.

    Without the precondition the `from y = 0` entry assertion is reachable, so
    the domains differ and the verdict is `partial`; with it, IC3 proves the
    whole thing.
    """
    loop = HEAD + "    from y = 0 do x += 1\n y += 1 until y = 3\n"
    closed = HEAD + "    x += 3\n    y += 3\n"
    self.assertEqual(self.check(loop, closed).status, "partial")
    self.assertEqual(self.check(loop, closed, assume="y = 0").status, "equivalent")

  def test_a_program_is_equivalent_to_itself(self):
    src = HEAD + "    x += y\n    y -= x\n"
    self.assertEqual(self.check(src, src).status, "equivalent")


if __name__ == "__main__":
  unittest.main()
