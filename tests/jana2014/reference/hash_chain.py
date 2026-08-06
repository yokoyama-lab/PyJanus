"""Four iterations of the non-injective map f(v) = (v*v + 1) mod 16.

Only the result is asserted: the preimage indices banked in `tr` are the history
that makes the iteration reversible, i.e. garbage.
"""

X, STEPS, MODULUS = 5, 4, 16


def f(value):
  return (value * value + 1) % MODULUS


def expected():
  x = X
  for _ in range(STEPS):
    x = f(x)
  return {"x": x}
