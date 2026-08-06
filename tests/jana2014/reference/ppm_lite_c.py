"""Order-1 context-adaptive canonical Huffman (PPM-lite).

Asserted: the source is consumed, and the 4x3 context frequency table is
scratch that comes back to zero. As with adaptive_huffman, the code assignment
among equally-frequent symbols is this encoder's convention, so the emitted
bits are not predicted here.
"""

GARBAGE = []

PARTIAL = "the emitted bits, for the same reason as adaptive_huffman"

S = [1, 2, 1, 2, 1]
CONTEXT_TABLE = 12


def expected():
  return {"s": [0] * len(S), "n": len(S), "cnt": [0] * CONTEXT_TABLE}
