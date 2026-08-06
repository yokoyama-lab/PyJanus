"""Adaptive canonical Huffman over the alphabet {1,2,3}, all counts starting 1.

Three symbols admit only one Huffman shape: the most frequent takes one bit and
the other two take two. The program fixes the two free choices, and they are
declared here rather than rediscovered -- ties in the frequency comparison go to
the higher symbol, and of the two losers the smaller gets `10`, the larger `11`.
Counts are updated after coding each symbol, so the decoder can follow along.

The source is consumed and the frequency table is uncomputed back to zero, which
is the "zero garbage" claim the program exists to make.
"""

GARBAGE = []

S = [1, 2, 1, 2, 1]
ALPHABET = (1, 2, 3)
BITS_WIDTH = 10


def winner(counts):
  """The symbol that gets the one-bit code; ties go to the higher symbol."""
  if counts[2] >= counts[1] and counts[2] >= counts[0]:
    return 3
  return 2 if counts[1] >= counts[0] else 1


def code(symbol, champion):
  if symbol == champion:
    return [0]
  other_loser = sum(ALPHABET) - champion - symbol
  return [1, 1 if symbol > other_loser else 0]


def expected():
  counts = [1] * len(ALPHABET)
  bits = []
  for symbol in S:
    bits += code(symbol, winner(counts))
    counts[symbol - 1] += 1
  return {
    "s": [0] * len(S), "n": len(S), "cnt": [0] * len(ALPHABET),
    "nbits": len(bits), "bits": bits + [0] * (BITS_WIDTH - len(bits)),
  }
