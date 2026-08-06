"""A 5-comparator sorting network for 4 elements, logging each swap decision.
The first call is undone; the second runs on sorted input, so nothing swaps."""

A = [4, 2, 3, 1]
B = [1, 2, 3, 4]
COMPARATORS = 5


def expected():
  return {"a": A, "log": [0] * COMPARATORS,
          "b": sorted(B), "log_b": [0] * COMPARATORS}
