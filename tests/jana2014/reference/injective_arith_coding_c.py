"""Arithmetic coding of a bit string, then decoded again."""

GARBAGE = []

M = [1, 0, 1, 0]


def expected():
  return {"m": M, "n": len(M), "x": 0, "q": 0, "r": 0}
