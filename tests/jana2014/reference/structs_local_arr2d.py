"""`local struct` over a struct with a 2-D array field."""

A = {"grid": [[1, 2], [3, 4]], "n": 10}


def expected():
  return {"a": A, "s": sum(sum(row) for row in A["grid"]) + A["n"]}
