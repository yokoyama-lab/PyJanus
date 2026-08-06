"""Binomial coefficient."""

from math import comb

N, R = 5, 2


def expected():
  return {"n": N, "r": R, "res": comb(N, R)}
