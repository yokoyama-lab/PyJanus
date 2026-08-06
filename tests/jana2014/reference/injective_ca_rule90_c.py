"""Second-order Rule 90 run three steps and stepped back again."""

GARBAGE = []

A = [0, 0, 0, 0, 0, 0, 0, 0]
B = [0, 0, 0, 0, 1, 0, 0, 0]
STEPS = 3


def expected():
  return {"a": A, "b": B, "n": len(A), "steps": STEPS}
