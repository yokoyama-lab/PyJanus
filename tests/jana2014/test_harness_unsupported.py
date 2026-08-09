"""The `differentialar` harness must report an input it cannot handle as
`Unsupported`, and as nothing else.

`differentialar.check()` documents `Unsupported` as the way a program outside
the extracted core is reported, and callers catch it to record a *skip*.  It is
raised in 23 places, so the contract is clearly intended -- but nothing enforced
it, and two input shapes escaped as a raw `TypeError` / `KeyError`:

  * `int A[] = {1, 2, 3}` parses with `dimensions == [None]` (the length comes
    from the initializer) and reached `int(d["value"])` unguarded;
  * `push(1, s)` carries no `lval` key on its operand node.

A harness that raises the wrong exception type turns "we did not check this"
into "this failed" -- or, with a broad `except`, into "no problem found".  These
tests pin the *type*, which is the part that was wrong; the message is only
checked loosely.
"""
from __future__ import annotations

import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "coq" / "harness"))

import differentialar                                    # noqa: E402


# Programs the harness is expected to decline, and why.  Keep this list append-
# only: each entry is a shape that once escaped as some other exception, or that
# we want to keep declining loudly.
UNSUPPORTED = {
  "array_without_a_dimension": (
    "procedure main()\n"
    "    int A[] = {1, 2, 3}\n"
    "    A[0] += 1\n"),
  "local_array_without_a_dimension": (
    "procedure main()\n"
    "    int b = 0\n"
    "    local int A[] = {1, 2, 3}\n"
    "        b += A[0]\n"
    "    delocal int A[] = {1, 2, 3}\n"),
  "push_of_a_literal": (
    "procedure main()\n"
    "    stack s = nil\n"
    "    int m = 0\n"
    "    push(1, s)\n"
    "    pop(m, s)\n"
    "    m -= 1\n"),
}


class HarnessUnsupportedTests(unittest.TestCase):

  def _translate(self, src: str) -> None:
    import tempfile
    with tempfile.NamedTemporaryFile("w", suffix=".j", delete=False) as f:
      f.write(src)
      path = f.name
    try:
      differentialar.translate(path)
    finally:
      Path(path).unlink(missing_ok=True)

  def test_declines_with_unsupported_and_nothing_else(self) -> None:
    for name, src in UNSUPPORTED.items():
      with self.subTest(program=name):
        try:
          self._translate(src)
        except differentialar.Unsupported:
          continue
        except Exception as e:                          # noqa: BLE001
          self.fail(f"{name}: leaked {type(e).__name__}: {e} "
                    f"(the harness must raise Unsupported)")
        self.fail(f"{name}: translated a program the harness cannot handle")

  def test_const_dims_accepts_constant_extents(self) -> None:
    # The guard must not swallow the ordinary case.
    self.assertEqual(
      differentialar.const_dims([{"value": 2}, {"value": 3}], "array"), [2, 3])

  def test_const_dims_rejects_a_missing_dimension(self) -> None:
    with self.assertRaises(differentialar.Unsupported):
      differentialar.const_dims([None], "array")

  def test_const_dims_rejects_a_computed_dimension(self) -> None:
    with self.assertRaises(differentialar.Unsupported):
      differentialar.const_dims([{"op": "+"}], "array")


if __name__ == "__main__":
  unittest.main()
