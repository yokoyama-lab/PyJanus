"""Factorial, input preserved."""

GARBAGE = []

from math import factorial

N = 5


def expected():
  return {"n": N, "res": factorial(N)}
