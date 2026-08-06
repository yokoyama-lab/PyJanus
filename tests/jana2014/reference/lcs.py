"""Longest common subsequence, leaving the whole DP table.
"ABCBDAB" and "BDCAB" over A=1 B=2 C=3 D=4, row-major with stride n+1."""

X = [1, 2, 3, 2, 4, 1, 2]
Y = [2, 4, 3, 1, 2]


def expected():
  m, n = len(X), len(Y)
  table = [[0] * (n + 1) for _ in range(m + 1)]
  for i in range(1, m + 1):
    for j in range(1, n + 1):
      if X[i - 1] == Y[j - 1]:
        table[i][j] = table[i - 1][j - 1] + 1
      else:
        table[i][j] = max(table[i - 1][j], table[i][j - 1])
  return {"m": m, "n": n, "x": [0] + X, "y": [0] + Y,
          "L": [cell for row in table for cell in row]}
