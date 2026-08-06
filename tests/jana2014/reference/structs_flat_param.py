"""A struct passed by reference: one procedure sums its fields into a scalar,
another scales the w field by a value argument."""


def expected():
  a = {"v": [2, 3, 5], "w": 7}
  r = sum(a["v"]) + a["w"]
  a["w"] += 4 * 2
  return {"a": a, "r": r}
