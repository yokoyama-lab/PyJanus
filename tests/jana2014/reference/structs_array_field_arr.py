"""An array of structs that themselves have array fields, read across elements."""


def expected():
  g = [{"v": [1, 2, 3], "sum": 0}, {"v": [4, 0, 0], "sum": 0}]
  g[1]["sum"] += g[0]["v"][2]
  g[0]["sum"] += g[1]["v"][0]
  return {"g": g}
