"""Growable array: append five, read one, pop two. Capacity doubles, never shrinks
back below what the deletions leave. The resize log `dbit` is garbage."""

ADDED = [10, 20, 30, 40, 50]
QUERY_AT = 2
DELETES = 2
BACKING = 16


def expected():
  data, cap = [], 1
  for value in ADDED:
    if len(data) == cap:
      cap *= 2
    data.append(value)
  q = data[QUERY_AT]
  popped = [data.pop() for _ in range(DELETES)]
  return {
    "data": data + [0] * (BACKING - len(data)),
    "length": len(data), "cap": cap, "q": q, "e": 0,
    "x1": popped[0], "x2": popped[1],
  }
