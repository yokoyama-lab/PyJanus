"""Dvoretzky and Motzkin's cycle lemma.

A sequence of +/-1 summing to 1 has exactly one cyclic rotation all of whose
prefix sums are positive; the program rotates to it and reports the shift.
"""

GARBAGE = []

A = [-1, 1, 1, -1, 1]


def rotate(seq, r):
  return seq[r:] + seq[:r]


def all_prefixes_positive(seq):
  total = 0
  for value in seq:
    total += value
    if total <= 0:
      return False
  return True


def expected():
  r = next(r for r in range(len(A)) if all_prefixes_positive(rotate(A, r)))
  return {"a": rotate(A, r), "n": len(A), "r": r}
