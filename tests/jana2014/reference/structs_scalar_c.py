"""Struct fields as lvalues: field-to-field addition, then a swap across structs."""

GARBAGE = []


def expected():
  p = {"x": 3, "y": 4}
  q = {"x": 10, "y": 0}
  p["x"] += p["y"]
  p["x"], q["x"] = q["x"], p["x"]
  return {"p": p, "q": q}
