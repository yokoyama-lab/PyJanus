"""Permutation -> Lehmer code -> integer, then both steps undone."""

GARBAGE = []

PERM = [2, 0, 3, 1]


def expected():
  return {"perm": PERM, "n": len(PERM), "int_result": 0}
