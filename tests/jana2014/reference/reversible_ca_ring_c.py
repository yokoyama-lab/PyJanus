"""Second-order Rule 90 on a ring: same half-step, with the neighbours wrapping."""

GARBAGE = []

A = [0, 0, 0, 0, 0]
B = [2, 0, 0, 0, 3]


def step(target, source):
  n = len(target)
  return [target[i] ^ source[(i - 1) % n] ^ source[(i + 1) % n] for i in range(n)]


def expected():
  a = step(A, B)
  b = step(B, a)
  return {"a": a, "b": b}
