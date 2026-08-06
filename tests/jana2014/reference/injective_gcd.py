"""Clean gcd (input preserved, quotients logged) at three inputs, the first of
which is uncalled away. gcd(0, n) = n."""

GARBAGE = ["log"]

from math import gcd

PAIRS = [(12, 18), (21, 14), (0, 9)]
LOG_WIDTH = 20


def expected():
  (a, b), (a2, b2), (a3, b3) = PAIRS
  return {"a": a, "b": b, "g": 0,
          "a2": a2, "b2": b2, "g2": gcd(a2, b2),
          "a3": a3, "b3": b3, "g3": gcd(a3, b3),
          "log": [0] * LOG_WIDTH}
