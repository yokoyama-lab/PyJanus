"""Second-order Rule 90 on a line: each half-step xors the other row's
neighbours into this one. Cells outside the line are zero."""

A = [0, 4, 5, 6, 0]
B = [0, 1, 2, 3, 0]


def step(target, source):
  out = list(target)
  for i in range(1, len(out) - 1):
    out[i] ^= source[i - 1] ^ source[i + 1]
  return out


def expected():
  a = step(A, B)
  b = step(B, a)
  return {"a": a, "b": b}
