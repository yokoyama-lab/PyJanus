"""The earlier matrix multiplication, with an explicit LDU workspace.

`crout(A, LDU)` writes A's packed decomposition into a separate matrix, the two
multiplications fold it into B from the *left*, and `uncall crout` clears the
workspace back to zero -- compute, use, uncompute, so A survives untouched and
LDU ends empty.

multLD applies the diagonal and the strict upper part with i descending;
multU then applies the strict lower part with i ascending.
"""

from _crout import decompose

GARBAGE = []

A = [[2, 4, 4], [4, 1, 1], [2, 3, 4]]
B = [[3, 2, 4], [1, 2, 1], [4, 3, 1]]
X, Y = 2, 4


def mult_ld(packed, right, n):
  out = [row[:] for row in right]
  for i in range(n - 1, -1, -1):
    for j in range(n):
      out[i][j] *= packed[i][i]
      for k in range(i - 1, -1, -1):
        out[i][j] += packed[k][i] * out[k][j]
  return out


def mult_u(packed, right, n):
  out = [row[:] for row in right]
  for i in range(n):
    for j in range(n):
      for k in range(i + 1, n):
        out[i][j] += packed[k][i] * out[k][j]
  return out


def expected():
  n = len(A)
  packed = decompose(A, n)
  product = mult_u(packed, mult_ld(packed, B, n), n)
  return {"A": A, "B": product, "LDU": [[0] * n for _ in range(n)],
          "n": n, "x": X, "y": Y}
