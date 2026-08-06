"""Bit-level injections: keyed xor (an involution), xor-into, Gray coding and a
Feistel round, the last two undone again."""

A, K, X, Y, GX, L, R, KEY = 12, 10, 240, 255, 12, 5, 7, 3


def expected():
  return {"a": A, "k": K, "x": X, "y": Y ^ X, "gx": GX, "g": 0,
          "L": L, "R": R, "K": KEY}
