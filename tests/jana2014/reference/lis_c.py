"""Longest increasing subsequence: the length ending at each position."""

GARBAGE = []

A = [10, 22, 9, 33, 21, 50, 41, 60]


def expected():
  lengths = []
  for i, value in enumerate(A):
    best = max((lengths[j] for j in range(i) if A[j] < value), default=0)
    lengths.append(best + 1)
  return {"a": A, "n": len(A), "L": lengths, "res": max(lengths)}
