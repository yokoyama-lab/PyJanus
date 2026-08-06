"""The three bitwise operators, on one pair of operands."""

GARBAGE = []

X, Y = 12, 10


def expected():
  return {"x": X, "y": Y, "a": X & Y, "o": X | Y, "e": X ^ Y}
