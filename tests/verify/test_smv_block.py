"""Pin `smv.py`'s large-block encoding to the shapes proved in Rocq.

`coq/RevSmvBlock.v` models the pending map that `_stmt` accumulates and proves

    block_sound     : sexec s g h -> forall x, seval g (p' x) = Some (h x)
    guard_at_entry  : describes g0 p g -> seval g0 (subst p c) = seval g c

— one transition carrying |vars| *simultaneous* updates over the block's entry
values denotes the same relation as running the block statement by statement,
and a guard met halfway through may be emitted as a term over entry values.
Those are the two risks `docs/totality-checking.md` §8.4 named as the reason the
large-block encoding could not be verified at the functor layer: the composition
order of the accumulated updates, and the state a path condition is evaluated in.

The proof is about the model; these tests are about the *emitted text*, so the
proof stays about the compiler that runs.  Each one mirrors a Rocq example:

* `test_the_documented_block_is_one_transition` / `..._accumulates` —
  `documented_block_accumulates`
* `test_a_swap_is_simultaneous` — `a_swap_must_be_simultaneous`
* `test_an_unwritten_variable_gets_no_next` — the [_edge] filter that makes the
  `TRUE` default absorb frame conditions
* `test_a_mid_block_guard_is_over_entry_values` — `guard_at_entry`
"""

from __future__ import annotations

from pathlib import Path
import re
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from jana_py import parser_jana2014
from jana_py import preprocess
from jana_py.smv import compile_to_smv

#: The block `docs/totality-checking.md` §2 quotes.
DOCUMENTED = ("procedure main()\n"
              "    int v\n    int g\n    int h\n    int halfg\n    int t\n"
              "    v += g\n"
              "    h -= v\n"
              "    h += halfg\n"
              "    t += 1\n")

SWAP = "procedure main()\n    int x\n    int y\n    x += 1\n    x <=> y\n"

MID_BLOCK_ASSERT = ("procedure main()\n    int x\n"
                    "    x += 1\n    assert(x = 1)\n    x += 1\n")


def model_of(src: str, **kw) -> str:
  pt = preprocess.preprocess_text("<test>", src, None, "jana2014")
  program = parser_jana2014.parse_program("<test>", pt.text, pt.line_origins)
  return compile_to_smv(program, **kw)


def next_branches(model: str, var: str) -> list[tuple[str, str]]:
  """The `(guard, value)` branches of `next(var)`, excluding the `TRUE` default."""
  out: list[tuple[str, str]] = []
  inside = False
  for line in model.splitlines():
    stripped = line.strip()
    if stripped == f"next({var}) := case":
      inside = True
      continue
    if inside:
      if stripped == "esac;":
        break
      m = re.match(r"(.*?) : (.*);$", stripped)
      assert m is not None, stripped
      if m.group(1) != "TRUE":
        out.append((m.group(1), m.group(2)))
  return out


def has_next(model: str, var: str) -> bool:
  return f"next({var}) := case" in model


class BlockShapeTests(unittest.TestCase):
  """Straight-line code becomes one transition, not one per statement."""

  def test_the_documented_block_is_one_transition(self):
    # Four assignments, one program location, one edge out of it.
    model = model_of(DOCUMENTED, init="zero")
    self.assertEqual(len(next_branches(model, "pc")), 1)

  def test_the_documented_block_accumulates_in_order(self):
    # `h` is decreased by the *accumulated* `v`, not by its entry value — this
    # is the exact term `documented_block_accumulates` proves and §2 quotes.
    model = model_of(DOCUMENTED, init="zero")
    self.assertEqual([v for _, v in next_branches(model, "h")],
                     ["((h - (v + g)) + halfg)"])
    self.assertEqual([v for _, v in next_branches(model, "v")], ["(v + g)"])
    self.assertEqual([v for _, v in next_branches(model, "t")], ["(t + 1)"])

  def test_an_unwritten_variable_gets_no_next(self):
    # `g` and `halfg` are only read, so `_edge` drops them and the `TRUE`
    # default absorbs their frame conditions.
    model = model_of(DOCUMENTED, init="zero")
    self.assertFalse(has_next(model, "g"))
    self.assertFalse(has_next(model, "halfg"))
    self.assertTrue(has_next(model, "h"))

  def test_a_swap_is_simultaneous(self):
    # `x <=> y` after `x += 1`: both updates are written against the *entry*
    # store, so `y` receives `x`'s accumulated value and `x` receives `y`.
    # Doing the two updates sequentially would give `y` its own value back —
    # `a_swap_must_be_simultaneous` / `the_sequential_swap_is_not_reversible`.
    model = model_of(SWAP, init="zero")
    self.assertEqual([v for _, v in next_branches(model, "x")], ["y"])
    self.assertEqual([v for _, v in next_branches(model, "y")], ["(x + 1)"])

  def test_a_mid_block_guard_is_over_entry_values(self):
    # `assert(x = 1)` sits between two updates; the emitted guard reads the
    # pending value `(x + 1)`, not the variable — `guard_at_entry`.
    model = model_of(MID_BLOCK_ASSERT, init="zero")
    guards = [g for g, _ in next_branches(model, "pc")]
    self.assertTrue(any("(x + 1) = 1" in g for g in guards), guards)
    self.assertFalse(any(re.search(r"[^+] x = 1", g) for g in guards), guards)

  def test_the_block_survives_the_guard(self):
    # ...and the update after the assertion composes on top of it, under the
    # same path condition.
    model = model_of(MID_BLOCK_ASSERT, init="zero")
    self.assertEqual([v for _, v in next_branches(model, "x")], ["((x + 1) + 1)"])


class BlockValueTests(unittest.TestCase):
  """`block_sound` executed: the accumulated term computes what Janus computes.

  The proof covers every store; this evaluates the emitted term on a grid and
  compares against the interpreter's arithmetic, the way `test_smv_expr.py`
  mirrors `mfdiv_correct`.
  """

  GRID = [-5, -1, 0, 1, 7]

  def test_the_accumulated_update_matches_sequential_execution(self):
    model = model_of(DOCUMENTED, init="zero")
    term = next_branches(model, "h")[0][1]
    for v in self.GRID:
      for g in self.GRID:
        for h in self.GRID:
          for halfg in self.GRID:
            with self.subTest(v=v, g=g, h=h, halfg=halfg):
              # one transition, read at the entry store
              block = eval(term, {}, {"v": v, "g": g, "h": h, "halfg": halfg})  # noqa: S307
              # the same statements, run one at a time
              sv, sh = v, h
              sv = sv + g
              sh = sh - sv
              sh = sh + halfg
              self.assertEqual(block, sh)


if __name__ == "__main__":
  unittest.main()
