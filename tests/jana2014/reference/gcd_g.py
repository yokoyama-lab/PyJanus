"""Greatest common divisor. The decision log is garbage, so it is not asserted."""

GARBAGE = ["log"]

from math import gcd

A, B = 48, 36


def expected():
  g = gcd(A, B)
  return {"a": g, "b": g}
