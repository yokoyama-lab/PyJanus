"""Cantor's pairing bijection N x N -> N."""

X, Y = 3, 5


def expected():
  z = (X + Y) * (X + Y + 1) // 2 + Y
  return {"x": X, "y": Y, "z": z}
