"""Burrows-Wheeler transform: last column of the sorted rotations, plus the
index the original string landed at. The input is consumed."""

GARBAGE = []

S = [1, 2, 1, 2, 1, 2]


def expected():
  n = len(S)
  rotations = sorted(range(n), key=lambda i: S[i:] + S[:i])
  return {
    "s": [0] * n,
    "n": n,
    "L": [S[(i + n - 1) % n] for i in rotations],
    "primary": rotations.index(0),
  }
