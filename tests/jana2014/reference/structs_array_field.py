"""A struct with an array field and a 2-D array field, read across elements."""

GARBAGE = []


def expected():
  a = {"v": [5, 7, 0], "grid": [[2, 0], [0, 4]], "w": 0}
  a["v"][2] += a["v"][0]
  a["grid"][0][1] += a["grid"][1][1]
  a["w"] += a["v"][1]
  return {"a": a}
