"""Clean divmod by compute-use-uncompute: divmod(17,5) is undone, divmod(3,5)
is kept."""

GARBAGE = []

X, D, X2 = 17, 5, 3


def expected():
  return {"x": X, "d": D, "q": 0, "r": 0,
          "x2": X2, "q2": X2 // D, "r2": X2 % D}
