"""Inversion code of a permutation: how many earlier entries are smaller."""

GARBAGE = []

X = [2, 0, 3, 1, 5, 4]


def expected():
  return {"x": [sum(1 for j in range(i) if X[j] < X[i]) for i in range(len(X))]}
