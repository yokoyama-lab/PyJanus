"""Matrix multiplication routed through a Crout LU decomposition.

`matrix_mult` would decompose B, fold L*D and then U into A from the right, and
recompose B -- giving A := A*B. `main` runs the decomposition the other way
round: it *un*composes B first and recomposes it at the end, so what gets folded
into A is the packing read back out twice.

multLD computes A := A*(L*D) column by column from the right, multU then
A := A*U with i descending so each column still sees the pre-update ones.
"""

from _crout import compose, decompose

GARBAGE = []

A = [[3, 2, 4], [1, 2, 1], [4, 3, 1]]
B = [[2, 4, 4], [4, 1, 1], [2, 3, 4]]


def mult_ld(left, packed, n):
  out = [row[:] for row in left]
  for i in range(n):
    for j in range(n):
      out[j][i] *= packed[i][i]
      for k in range(i + 1, n):
        out[j][i] += packed[k][i] * out[j][k]
  return out


def mult_u(left, packed, n):
  out = [row[:] for row in left]
  for i in range(n - 1, -1, -1):
    for j in range(n):
      for k in range(i):
        out[j][i] += packed[k][i] * out[j][k]
  return out


def expected():
  n = len(A)
  unpacked = compose(B, n)
  product = mult_u(mult_ld(A, unpacked, n), unpacked, n)
  return {"A": product, "B": decompose(unpacked, n), "n": n}
