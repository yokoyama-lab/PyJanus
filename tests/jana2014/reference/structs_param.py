"""A struct passed with a value argument: shift adds d to x and d-... to y,
then swapfields exchanges them; the third call is uncalled away."""

GARBAGE = []


def expected():
  a = {"x": 1 + 5, "y": 2 + 5}
  a["x"], a["y"] = a["y"], a["x"]
  return {"a": a, "b": {"x": 10, "y": 0}}
