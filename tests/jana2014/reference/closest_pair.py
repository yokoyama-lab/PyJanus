"""Closest pair of points, reported as a squared distance."""

POINTS = [(2, 3), (12, 30), (40, 50), (5, 1), (12, 10)]
BIG = 1000000


def expected():
  best = min(
    (ax - bx) ** 2 + (ay - by) ** 2
    for i, (ax, ay) in enumerate(POINTS)
    for bx, by in POINTS[i + 1:]
  )
  return {"res": best, "n": len(POINTS), "big": BIG,
          "x": [p[0] for p in POINTS], "y": [p[1] for p in POINTS]}
