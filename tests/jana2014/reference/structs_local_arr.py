"""`local struct` over a struct with an array field."""

A = {"v": [10, 20, 30], "w": 5}


def expected():
  return {"a": A, "s": sum(A["v"]) + A["w"]}
