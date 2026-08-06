"""Lomuto partition recording each comparison in a flag bit.

The first call is undone. The second runs on an already-sorted array, where the
pivot is the last element and every comparison succeeds.
"""

A = [3, 8, 2, 5, 1, 4, 7, 6]
B = [1, 2, 3, 4]


def partition(values):
  pivot = values[-1]
  flags = [1 if value <= pivot else 0 for value in values[:-1]] + [0]
  index = sum(flags)
  return sorted(values[:index]) + values[index:], flags, index


def expected():
  partitioned_b, flags_b, q = partition(B)
  return {"a": A, "flags": [0] * len(A), "p": 0,
          "b": partitioned_b, "flags_b": flags_b, "q": q}
