"""Merge sort with the stable sorting permutation left in `ord`."""

A = [5, 2, 4, 7, 1, 3, 2, 6]


def expected():
  order = sorted(range(len(A)), key=lambda i: (A[i], i))
  return {"a": sorted(A), "ord": order, "p": 0, "r": len(A) - 1}
