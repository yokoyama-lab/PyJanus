"""Crout LU decomposition, packed into one matrix the way both matrixmult
examples do it: the lower triangle including the diagonal holds L*D, the strict
upper triangle holds U, whose diagonal is an implicit 1.

Janus integer division truncates toward zero, so the reconstruction is exact
only when the decomposition divides evenly; these fixtures are chosen so it does.
"""


def truncated_div(a, b):
  quotient = abs(a) // abs(b)
  return quotient if (a < 0) == (b < 0) else -quotient


def decompose(matrix, n):
  packed = [row[:] for row in matrix]
  for j in range(n):
    for i in range(j, n):
      for k in range(j):
        packed[i][j] -= packed[i][k] * packed[k][j]
    for i in range(j + 1, n):
      for k in range(j):
        packed[j][i] -= packed[j][k] * packed[k][i]
      packed[j][i] = truncated_div(packed[j][i], packed[j][j])
  return packed


def compose(packed, n):
  """The inverse of `decompose`, i.e. L*D*U read back out of the packing."""
  matrix = [row[:] for row in packed]
  for j in range(n - 1, -1, -1):
    for i in range(n - 1, j, -1):
      matrix[j][i] *= matrix[j][j]
      for k in range(j - 1, -1, -1):
        matrix[j][i] += matrix[j][k] * matrix[k][i]
    for i in range(n - 1, j - 1, -1):
      for k in range(j - 1, -1, -1):
        matrix[i][j] += matrix[i][k] * matrix[k][j]
  return matrix
