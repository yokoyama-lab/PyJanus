"""Rank a balanced bit string, then unrank it: the round trip restores it and
clears the index."""

B = [1, 0, 1, 1, 1, 0, 0, 0]
N = 4


def expected():
  return {"b": B, "n": N, "index": 0}
