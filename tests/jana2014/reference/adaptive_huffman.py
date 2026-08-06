"""Adaptive canonical Huffman over the alphabet {1,2,3}, all counts starting 1.

Asserted: the source is consumed into the bit stream, and the frequency table
is uncomputed back to zero -- the "zero garbage" claim the program is written to
demonstrate. The bit stream itself is not: which of the two losing symbols gets
`10` and which gets `11` is a choice this encoder makes, not something adaptive
Huffman determines, so an independent implementation cannot predict it.
"""

GARBAGE = []

PARTIAL = "the emitted bits: which losing symbol gets `10` and which `11` is this encoder's convention"

S = [1, 2, 1, 2, 1]
COUNTERS = 3


def expected():
  return {"s": [0] * len(S), "n": len(S), "cnt": [0] * COUNTERS}
