"""Integer square root: the root, with the remainder left in place of the input."""

GARBAGE = ["num"]

from math import isqrt

NUM = 66


def expected():
  root = isqrt(NUM)
  return {"root": root, "num": NUM - root * root}
