"""The Ackermann function at (2, 2), with both arguments left intact.

  A(0, n) = n + 1;  A(m, 0) = A(m-1, 1);  A(m, n) = A(m-1, A(m, n-1))

Nothing about the definition is reversible; the Janus program gets there by
recomputing its intermediate values away rather than by keeping them, so the
answer here is just the function.
"""

GARBAGE = []

M, N = 2, 2


def ackermann(m, n):
  if m == 0:
    return n + 1
  if n == 0:
    return ackermann(m - 1, 1)
  return ackermann(m - 1, ackermann(m, n - 1))


def expected():
  return {"m": M, "n": N, "r": ackermann(M, N)}
