"""accumulate(p, q) does p += 2q + something; called, uncalled, called again,
so the net effect is one application."""


def expected():
  p, q = {"x": 1, "y": 2}, {"x": 10, "y": 20}
  return {"p": {"x": p["x"] + 2 * q["x"], "y": p["y"] + 2 * q["y"]}, "q": q}
