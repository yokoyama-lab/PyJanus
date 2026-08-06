"""Levenshtein distance, leaving the whole DP table.

"kitten" and "sitting" over the alphabet k=1 i=2 t=3 e=4 n=5 s=6 g=7. The table
is (m+1) x (n+1) laid out row-major with stride n+1 inside a 64-cell array.
"""

GARBAGE = []

X = [1, 2, 3, 3, 4, 5]
Y = [6, 2, 3, 3, 2, 5, 7]
CELLS = 64


def expected():
  m, n = len(X), len(Y)
  stride = n + 1
  table = [[0] * stride for _ in range(m + 1)]
  for i in range(m + 1):
    table[i][0] = i
  for j in range(stride):
    table[0][j] = j
  for i in range(1, m + 1):
    for j in range(1, stride):
      cost = 0 if X[i - 1] == Y[j - 1] else 1
      table[i][j] = min(table[i - 1][j] + 1, table[i][j - 1] + 1, table[i - 1][j - 1] + cost)
  flat = [cell for row in table for cell in row]
  return {
    "m": m, "n": n,
    "x": [0] + X + [0], "y": [0] + Y,
    "D": flat + [0] * (CELLS - len(flat)),
  }
