"""Order-1 context-adaptive canonical Huffman (PPM-lite).

The same three-symbol coder as adaptive_huffman, but with one frequency table
per context, the context being the previous symbol (0 before the first). Four
contexts times three symbols is the 4x3 table, which starts all-ones and is
returned entirely to zero.
"""

GARBAGE = []

S = [1, 2, 1, 2, 1]
ALPHABET = (1, 2, 3)
CONTEXTS = 4
BITS_WIDTH = 10


def winner(counts, context):
  base = context * len(ALPHABET)
  if counts[base + 2] >= counts[base + 1] and counts[base + 2] >= counts[base]:
    return 3
  return 2 if counts[base + 1] >= counts[base] else 1


def code(symbol, champion):
  if symbol == champion:
    return [0]
  other_loser = sum(ALPHABET) - champion - symbol
  return [1, 1 if symbol > other_loser else 0]


def expected():
  counts = [1] * (CONTEXTS * len(ALPHABET))
  bits, context = [], 0
  for symbol in S:
    bits += code(symbol, winner(counts, context))
    counts[context * len(ALPHABET) + symbol - 1] += 1
    context = symbol
  return {
    "s": [0] * len(S), "n": len(S), "cnt": [0] * len(counts),
    "nbits": len(bits), "bits": bits + [0] * (BITS_WIDTH - len(bits)),
  }
