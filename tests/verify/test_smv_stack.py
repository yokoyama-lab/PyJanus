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

The encoding side of each line lands in item 39; when it does, the `Encoding`
class below stops being skipped.
"""
import pathlib
import subprocess
import sys
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from jana_py.smv import SmvUnsupported, compile_to_smv  # noqa: E402
from jana_py import parser_jana2014, preprocess         # noqa: E402


def run(src: str) -> tuple[int, str]:
  proc = subprocess.run([sys.executable, "-m", "jana_py.cli", "--std", "jana2014", "-s", "-"],
                        input=src, capture_output=True, text=True, cwd=ROOT, timeout=120)
  return proc.returncode, proc.stdout + proc.stderr


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


class Encoding(unittest.TestCase):
  """Item 39 turns these on. Until then the checker refuses stacks, and this
  test says so explicitly rather than leaving the gap silent."""

  def test_a_stack_is_still_outside_the_fragment(self):
    self.assertFalse(compiles(PUSH),
                     "if this starts passing, item 39 landed — replace this "
                     "test with the encoding's own, do not delete it")


if __name__ == "__main__":
  unittest.main()
