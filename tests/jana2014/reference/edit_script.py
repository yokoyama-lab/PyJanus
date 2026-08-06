"""Levenshtein distance that consumes both strings.

The distance is asserted. `tr` is the symbol-carrying edit script -- the
embedding invented to make the computation injective, so it is garbage, and its
layout is a property of this encoding rather than of the distance.
"""

S = [1, 2, 1]
T = [2, 1]


def expected():
  previous = list(range(len(T) + 1))
  for i, a in enumerate(S, start=1):
    current = [i]
    for j, b in enumerate(T, start=1):
      current.append(min(previous[j] + 1, current[j - 1] + 1,
                         previous[j - 1] + (a != b)))
    previous = current
  return {"s": [0] * len(S), "m": len(S), "t": [0] * len(T), "n": len(T),
          "d": previous[-1]}
