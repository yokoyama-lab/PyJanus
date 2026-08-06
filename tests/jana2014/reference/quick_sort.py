"""Quicksort with the sorting permutation carried alongside."""

A = [2, 8, 7, 1, 3, 5, 6, 4]


def expected():
  return {"a": sorted(A), "ord": sorted(range(len(A)), key=lambda i: (A[i], i))}
