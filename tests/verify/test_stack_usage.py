"""`tools/stack_usage.py` decides whether a stack's depth is statically bounded.

That decision is the input to a design question a human still owes an answer to
(`docs/loop-queue.md`: encode stacks, and if so with what depth), so getting it
wrong misinforms the decision rather than breaking a build — nothing else would
catch it.  The first version was wrong in exactly the way that matters: it asked
whether the procedure holding the `push` was itself recursive or looping.
`hanoi_c` pushes in `move`, which is neither; it is *called by* the recursion.
That program came out "statically bounded", the opposite of true.

So the property under test is the propagation: a push is unbounded when the
procedure holding it can be reached from a cycle or from a call inside a loop.
"""
import pathlib
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "tools"))

import stack_usage  # noqa: E402


def analyse(src: str) -> dict:
  with tempfile.TemporaryDirectory() as d:
    p = pathlib.Path(d) / "prog.ja"
    p.write_text(src, encoding="utf-8")
    got = stack_usage.usage(p)
  assert got is not None, "the fixture declares no stack"
  return got


STRAIGHT_LINE = """
procedure main()
    stack a
    int d
    d += 1
    push(d, a)
"""

PUSH_IN_LOOP = """
procedure main()
    stack a
    int d
    int i
    from i = 0 do
        d += 1
        push(d, a)
        i += 1
    loop skip
    until i = 5
"""

# `move` is neither recursive nor inside a loop; the recursion calls it.
HANOI_SHAPE = """
procedure move(stack dst)
    local int d = 0
        d += 1
        push(d, dst)
        d -= 1
    delocal int d = 0

procedure rec(int n, stack dst)
    if n = 0 then
        skip
    else
        n -= 1
        call rec(n, dst)
        call move(dst)
        n += 1
    fi n = 0

procedure main()
    stack a
    int n
    n += 3
    call rec(n, a)
"""

CALLED_FROM_A_LOOP = """
procedure once(stack dst)
    local int d = 0
        d += 1
        push(d, dst)
        d -= 1
    delocal int d = 0

procedure main()
    stack a
    int i
    from i = 0 do
        call once(a)
        i += 1
    loop skip
    until i = 4
"""

CALLED_ONCE = """
procedure once(stack dst)
    local int d = 0
        d += 1
        push(d, dst)
        d -= 1
    delocal int d = 0

procedure main()
    stack a
    call once(a)
"""


class BoundedDepth(unittest.TestCase):
  def test_a_straight_line_push_is_bounded(self):
    self.assertEqual(analyse(STRAIGHT_LINE)["push_unbounded"], 0)

  def test_a_push_through_one_call_is_bounded(self):
    r = analyse(CALLED_ONCE)
    self.assertEqual((r["push_in_loop"], r["push_unbounded"]), (0, 0))


class UnboundedDepth(unittest.TestCase):
  def test_a_push_inside_a_loop_is_unbounded(self):
    self.assertEqual(analyse(PUSH_IN_LOOP)["push_in_loop"], 1)

  def test_a_push_in_a_procedure_called_from_a_loop_is_unbounded(self):
    r = analyse(CALLED_FROM_A_LOOP)
    self.assertEqual(r["push_in_loop"], 0, "the push is not syntactically in a loop")
    self.assertEqual(r["push_unbounded"], 1, "but its procedure is called from one")

  def test_the_hanoi_shape_is_unbounded(self):
    """The regression: recursion reaches the pusher without being it."""
    r = analyse(HANOI_SHAPE)
    self.assertEqual(r["push_in_loop"], 0)
    self.assertEqual(r["push_unbounded"], 1,
                     "a push reached by recursion must not count as bounded")


class TheRealCorpus(unittest.TestCase):
  def test_hanoi_is_not_reported_as_bounded(self):
    p = ROOT / "tests/jana2014/fixtures/examples/hanoi_c.ja"
    r = stack_usage.usage(p)
    self.assertIsNotNone(r)
    self.assertGreater(r["push_unbounded"], 0)


if __name__ == "__main__":
  unittest.main()
