"""0/1 knapsack, leaving the whole DP table, row-major with stride cap+1."""

GARBAGE = []

WEIGHTS = [2, 3, 4]
VALUES = [3, 4, 5]
CAP = 5


def expected():
  n = len(WEIGHTS)
  table = [[0] * (CAP + 1) for _ in range(n + 1)]
  for i in range(1, n + 1):
    for c in range(CAP + 1):
      table[i][c] = table[i - 1][c]
      if WEIGHTS[i - 1] <= c:
        table[i][c] = max(table[i][c], table[i - 1][c - WEIGHTS[i - 1]] + VALUES[i - 1])
  return {"n": n, "cap": CAP, "wt": [0] + WEIGHTS, "val": [0] + VALUES,
          "K": [cell for row in table for cell in row]}
