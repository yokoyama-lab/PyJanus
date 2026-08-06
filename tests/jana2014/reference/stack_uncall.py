"""Two `build`s and one `uncall build`: the second run is popped back off."""

FIRST = [100, 101, 102]


def expected():
  return {"s": list(reversed(FIRST))}
