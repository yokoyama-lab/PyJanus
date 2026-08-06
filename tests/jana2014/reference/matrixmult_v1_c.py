"""The earlier matrix multiplication, with an explicit LDU workspace.

Asserted: A survives the round trip through `crout` and its `uncall`, and the
LDU workspace is left entirely zero -- the compute-use-uncompute property the
program exists to show. As in matrixmult_c.ja, the accumulated product is left to
that program's own convention.
"""

GARBAGE = []

PARTIAL = "the product accumulated into B, for the same reason as matrixmult"

A = [[2, 4, 4], [4, 1, 1], [2, 3, 4]]
X, Y = 2, 4


def expected():
  return {"A": A, "LDU": [[0] * len(A) for _ in A], "n": len(A), "x": X, "y": Y}
