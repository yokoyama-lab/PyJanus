"""Push 1..5, then reverse the stack. Stacks read top first."""

GARBAGE = []

PUSHED = [1, 2, 3, 4, 5]


def expected():
  top_first = list(reversed(PUSHED))
  return {"s": list(reversed(top_first))}
