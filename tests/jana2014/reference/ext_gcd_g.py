"""Extended Euclid: the two Bezout columns, carried to the end of the recursion.

(x0, y0) is the pair with A*x0 + B*y0 = gcd; (x1, y1) spans the kernel.
"""

GARBAGE = ["qlog"]

A, B = 240, 46


def expected():
  x0, x1, y0, y1, a, b = 1, 0, 0, 1, A, B
  while b:
    q, r = divmod(a, b)
    a, b = b, r
    x0, x1 = x1, x0 - q * x1
    y0, y1 = y1, y0 - q * y1
  return {"a": a, "b": 0, "x0": x0, "x1": x1, "y0": y0, "y1": y1}
