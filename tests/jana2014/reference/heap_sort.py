"""Heapsort, in place over a[1..sz]. The decision stack `gb` is garbage."""

KEYS = [4, 1, 3, 2, 16, 9, 10, 14, 8, 7]
CELLS = 17


def expected():
  ordered = [0] + sorted(KEYS)
  return {"a": ordered + [0] * (CELLS - len(ordered)), "sz": len(KEYS)}
