"""Counting sort. `c` ends as the exclusive prefix sums of the key counts."""

A = [2, 5, 3, 0, 2, 3, 0, 3]
K = 6


def expected():
  counts = [A.count(key) for key in range(K)]
  offsets, running = [], 0
  for count in counts:
    offsets.append(running)
    running += count
  return {"a": A, "b": sorted(A), "c": offsets, "n": len(A), "k": K}
