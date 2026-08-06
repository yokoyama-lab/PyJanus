"""Selection sort recording how far ahead each pass found its minimum.

The offsets fit in fewer cells than a permutation would, which is the point of
the encoding; they are also exactly what `uncall` needs to undo the swaps.
"""

GARBAGE = ["tr"]

A = [3, 1, 2, 1, 2]


def expected():
  values = list(A)
  offsets = []
  for i in range(len(values)):
    smallest = min(range(i, len(values)), key=lambda j: values[j])
    offsets.append(smallest - i)
    values[i], values[smallest] = values[smallest], values[i]
  return {"a": values, "n": len(A), "tr": offsets}
