"""A stack machine (push / add / halt) run forwards and then uncalled, which
empties the stack and clears everything it produced."""

OPS = [0, 0, 1, 0, 2]
ARGS = [5, 3, 0, 10, 0]


def expected():
  return {"ops": OPS, "args": ARGS, "n": len(OPS),
          "s": [], "top_val": 0, "below": 0, "empty_check": 0}
