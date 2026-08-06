"""Inverse Burrows-Wheeler by LF-mapping, then uncalled: every workspace array
returns to zero and the input is restored."""

L = [1, 2, 3, 1, 0]
I, N, ALPHABET = 4, 5, 4


def expected():
  return {"L": L, "I": I, "n": N, "A": ALPHABET,
          "cnt": [0] * ALPHABET, "C": [0] * ALPHABET, "occ": [0] * ALPHABET,
          "T": [0] * N, "path": [0] * N, "s": [0] * N}
