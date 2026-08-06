"""Jarvis march: which points lie on the convex hull. `hseq` is the traversal
history the reversible version keeps, so it is not asserted."""

GARBAGE = ["hseq"]

POINTS = [(1, 1), (9, 2), (5, 4), (8, 9), (2, 7), (4, 2)]


def cross(o, a, b):
  return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])


def expected():
  n = len(POINTS)
  start = min(range(n), key=lambda i: POINTS[i])
  hull, current = [], start
  while True:
    hull.append(current)
    candidate = (current + 1) % n
    for other in range(n):
      if cross(POINTS[current], POINTS[candidate], POINTS[other]) < 0:
        candidate = other
    current = candidate
    if current == start:
      break
  return {
    "n": n, "start": start,
    "x": [p[0] for p in POINTS], "y": [p[1] for p in POINTS],
    "hull": [1 if i in hull else 0 for i in range(n)],
  }
