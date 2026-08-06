"""Bubble sort. The permutation `ord` is the garbage, so it is not asserted."""

GARBAGE = ["ord"]

A = [50, 20, 40, 60, 10, 30]


def expected():
  return {"a": sorted(A), "sz": len(A)}
