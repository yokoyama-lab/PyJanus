"""Selection sort recording, for each pass, how far ahead the minimum was.

That offset sequence is a factorial-base numeral (offset i is a digit in
0..n-1-i), which is what makes the sort reversible.
"""

A = [50, 20, 40, 60, 10, 30]


def expected():
  values = list(A)
  offsets = []
  for i in range(len(values)):
    smallest = min(range(i, len(values)), key=lambda j: values[j])
    offsets.append(smallest - i)
    values[i], values[smallest] = values[smallest], values[i]
  return {"a": values, "n": len(A), "ftab": offsets, "p": [0] * len(A)}
