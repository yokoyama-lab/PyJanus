"""Insertion sort into a fresh array; the input is preserved."""

GARBAGE = []

A = [50, 20, 40, 60, 10, 30]


def expected():
  return {"a": A, "b": sorted(A), "n": len(A)}
