"""Hamming weight of a vector of 8-bit words, and Hamming distance to another.

Both are clean accumulations: the words are read, never written, so the counts
add into fresh cells and subtract back out again.
"""

GARBAGE = []

A = [11, 15, 1, 128]
B = [10, 0, 3, 128]


def popcount(word):
  return bin(word).count("1")


def expected():
  weight = sum(popcount(word) for word in A)
  return {"a": A, "b": B, "len": len(A), "weight": weight,
          "dist": sum(popcount(x ^ y) for x, y in zip(A, B)),
          "parity": weight % 2}
