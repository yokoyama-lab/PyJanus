"""What a Janus stack actually does, measured before anything encodes it.

Every unsoundness this project has found came from a place where the encoding
was written from what the author believed the language does: swap had no
aliasing check, the modular modes were ignored, output statements were read as
not touching the store. So the stack semantics are pinned here first, against
the interpreter, and `jana_py/smv.py` gets to be written against these tests
rather than against a recollection.

The measurements are in `docs/totality-checking.md` §19. Two of them contradict
what a reader would guess from the array case:

* `top` does NOT consume, but it DOES fail on an empty stack — an expression
  with an ERR edge.
* two formals bound to one stack is FINE (`call two(s, s)` runs), where two
  formals on one scalar is an aliasing error. Flagging it would reject
  `reverse`, which the corpus contains.

The encoding landed in item 39 (2026-08-09); the `Encoding` class checks it
against these same shapes.
"""
import pathlib
import subprocess
import sys
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from jana_py.smv import BOUND_LOC, SmvUnsupported, compile_to_smv  # noqa: E402
from jana_py import nuxmv, parser_jana2014, preprocess  # noqa: E402


def run(src: str) -> tuple[int, str]:
  proc = subprocess.run([sys.executable, "-m", "jana_py.cli", "--std", "jana2014", "-s", "-"],
                        input=src, capture_output=True, text=True, cwd=ROOT, timeout=120)
  return proc.returncode, proc.stdout + proc.stderr


def model_of(src: str) -> str:
  pt = preprocess.preprocess_text("<test>", src, None, "jana2014")
  program = parser_jana2014.parse_program("<test>", pt.text, pt.line_origins)
  return compile_to_smv(program, init="zero")


def has_err_edge(model: str) -> bool:
  """A real transition into ERR, not the comment naming the location."""
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


def compiles(src: str) -> bool:
  pt = preprocess.preprocess_text("<test>", src, None, "jana2014")
  program = parser_jana2014.parse_program("<test>", pt.text, pt.line_origins)
  try:
    compile_to_smv(program, init="zero")
    return True
  except SmvUnsupported:
    return False


PUSH = """
procedure main()
    stack s
    int x
    x += 7
    push(x, s)
"""

POP_NONZERO = """
procedure main()
    stack s
    int x
    int y
    x += 7
    push(x, s)
    y += 3
    pop(y, s)
"""

POP_EMPTY = """
procedure main()
    stack s
    int x
    pop(x, s)
"""

TOP_EMPTY = """
procedure main()
    stack s
    int x
    x += top(s)
"""

TOP_KEEPS = """
procedure main()
    stack s
    int x
    int y
    x += 7
    push(x, s)
    y += top(s)
"""

SIZE_AND_EMPTY = """
procedure main()
    stack s
    int x
    x += size(s)
    x += 10 * empty(s)
"""

BY_REFERENCE = """
procedure fill(stack t)
    local int v = 0
        v += 5
        push(v, t)
    delocal int v = 0

procedure main()
    stack s
    call fill(s)
"""

UNCALL_INVERTS = BY_REFERENCE + """    uncall fill(s)
"""

TWO_FORMALS_ONE_STACK = """
procedure two(stack a, stack b)
    local int v = 0
        v += 5
        push(v, a)
        pop(v, b)
        v -= 5
    delocal int v = 0

procedure main()
    stack s
    call two(s, s)
"""


class Semantics(unittest.TestCase):
  """Measured 2026-08-09. Each of these is a line the encoding has to match."""

  def test_push_zeroes_its_source(self):
    rc, out = run(PUSH)
    self.assertEqual(rc, 0, out)
    self.assertIn("s = <7]", out)
    self.assertIn("x = 0", out, "push must clear the variable it consumed")

  def test_popping_into_a_non_zero_variable_fails(self):
    rc, out = run(POP_NONZERO)
    self.assertEqual(rc, 1)
    self.assertIn("Can't pop to non-zero variable", out)

  def test_popping_an_empty_stack_fails(self):
    rc, out = run(POP_EMPTY)
    self.assertEqual(rc, 1)
    self.assertIn("Can't pop from empty stack", out)

  def test_top_of_an_empty_stack_fails(self):
    """An expression that can fail — the encoding needs an ERR edge for it."""
    rc, out = run(TOP_EMPTY)
    self.assertEqual(rc, 1)
    self.assertIn("Can't pop from empty stack", out)

  def test_top_does_not_consume(self):
    rc, out = run(TOP_KEEPS)
    self.assertEqual(rc, 0, out)
    self.assertIn("s = <7]", out)
    self.assertIn("y = 7", out)

  def test_size_counts_and_empty_is_one_when_empty(self):
    rc, out = run(SIZE_AND_EMPTY)
    self.assertEqual(rc, 0, out)
    self.assertIn("x = 10", out, "size 0 plus 10 * empty(s) = 1")

  def test_a_stack_argument_is_passed_by_reference(self):
    rc, out = run(BY_REFERENCE)
    self.assertEqual(rc, 0, out)
    self.assertIn("s = <5]", out)

  def test_uncall_undoes_the_pushes(self):
    rc, out = run(UNCALL_INVERTS)
    self.assertEqual(rc, 0, out)
    self.assertIn("s = nil", out)

  def test_two_formals_on_one_stack_is_allowed(self):
    """Unlike two formals on one scalar. Rejecting this would reject
    `reverse` in the corpus, which is a correct program."""
    rc, out = run(TWO_FORMALS_ONE_STACK)
    self.assertEqual(rc, 0, out)
    self.assertIn("s = nil", out)


DEPTH_OVERFLOW = """
procedure main()
    stack s
    int x
""" + "    x += 1\n    push(x, s)\n" * 9

SIZE_OF_AN_ARRAY = """
procedure main()
    int a[4]
    int n
    n += size(a)
"""

LOCAL_STACK = """
procedure main()
    stack s
    int x
    local stack t = nil
        x += 3
        push(x, t)
        pop(x, t)
    delocal stack t = nil
"""


class Encoding(unittest.TestCase):
  """Item 39 landed 2026-08-09. Replaced the "still refused" pin rather than
  deleting it, so the boundary is fixed from the other side now."""

  def test_every_measured_shape_compiles(self):
    for name, src in [("push", PUSH), ("pop", POP_NONZERO), ("top", TOP_KEEPS),
                      ("size/empty", SIZE_AND_EMPTY), ("by reference", BY_REFERENCE),
                      ("two formals", TWO_FORMALS_ONE_STACK), ("local", LOCAL_STACK)]:
      with self.subTest(name):
        self.assertTrue(compiles(src))

  def test_size_still_works_on_an_array(self):
    """`size` is polymorphic — PyJanus takes an array as well as a stack.

    Making every stack expression an error on a non-stack turned
    `perm_to_code_c.ja`, which runs, into `refuted`. The corpus scan found it;
    nothing smaller would have.
    """
    rc, out = run(SIZE_OF_AN_ARRAY)
    self.assertEqual(rc, 0, out)
    self.assertIn("n = 4", out)
    self.assertFalse(has_err_edge(model_of(SIZE_OF_AN_ARRAY)),
                     "an array's size is not an error")

  def test_the_three_runtime_errors_are_err_edges(self):
    """ERR means the program fails. Measured in §19: popping empty, popping
    into a non-zero variable, and `top` of an empty stack."""
    for name, src in [("pop empty", POP_EMPTY), ("pop non-zero", POP_NONZERO),
                      ("top empty", TOP_EMPTY)]:
      with self.subTest(name):
        self.assertTrue(has_err_edge(model_of(src)), f"{name} must reach ERR")

  def test_overflowing_the_depth_is_bound_not_err(self):
    """BOUND means the MODEL stops following, not that the program fails.
    Merging the two would report a modelling limit as an accusation — which is
    what `Result.status` did before it could be asked per property."""
    model = model_of(DEPTH_OVERFLOW)
    self.assertIn(f"INVARSPEC pc != {BOUND_LOC}", model)

  @unittest.skipUnless(nuxmv.find_nuxmv(), "needs nuXmv")
  def test_a_correct_program_cannot_reach_err(self):
    """The no-false-alarm property, and it has to be asked of the checker.

    A syntactic "has an ERR edge" test fails here for the wrong reason: the
    `delocal` obligation emits a guarded edge in every correct program too.
    What matters is whether ERR is REACHABLE, which is nuXmv's question.
    """
    res = nuxmv.check(model_of(BY_REFERENCE), timeout=120)
    self.assertEqual(res.status_of("pc != 0"), "proved",
                     "the interpreter runs this; a reachable ERR is a false alarm")

  @unittest.skipUnless(nuxmv.find_nuxmv(), "needs nuXmv")
  def test_overflow_reaches_bound_but_not_err(self):
    """The distinction the whole design rests on, checked end to end."""
    res = nuxmv.check(model_of(DEPTH_OVERFLOW), timeout=120)
    self.assertEqual(res.status_of("pc != 0"), "proved", "the program does not fail")
    self.assertEqual(res.status_of("pc != 1"), "refuted", "the model runs out of depth")


if __name__ == "__main__":
  unittest.main()
