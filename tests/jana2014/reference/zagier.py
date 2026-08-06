"""Zagier's involution on triples with x^2 + 4yz fixed -- the one-sentence proof
that a prime 1 mod 4 is a sum of two squares."""

GARBAGE = []

X, Y, Z = 3, 1, 7


def expected():
  x, y, z = X, Y, Z
  if x < y - z:
    x, y, z = x + 2 * z, z, y - x - z
  elif x < 2 * y:
    x, y, z = 2 * y - x, y, x - y + z
  else:
    x, y, z = x - 2 * y, x - y + z, y
  return {"x": x, "y": y, "z": z}
