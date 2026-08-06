"""Streaming rANS over a binary alphabet: f = [1, 3], M = 4, state in [4, 8).

Encoding a symbol is x := (x div f)*M + c + (x mod f), preceded by shifting low
bits out of the state until it is small enough for the step to stay in range.
"""

GARBAGE = []

S = [2, 2, 1, 2, 2, 2]
FREQ = {1: 1, 2: 3}
CUM = {1: 0, 2: 1}
M, LOW = 4, 4
BITS_WIDTH = 12


def expected():
  x, bits = LOW, []
  for symbol in S:
    f, c = FREQ[symbol], CUM[symbol]
    while x >= 2 * f:
      bits.append(x % 2)
      x //= 2
    x = (x // f) * M + c + (x % f)
  return {"s": [0] * len(S), "n": len(S), "x": x, "nbits": len(bits),
          "bits": bits + [0] * (BITS_WIDTH - len(bits))}
