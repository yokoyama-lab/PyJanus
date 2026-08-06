"""Factorial, integer power and Horner evaluation, each uncalled away again."""

GARBAGE = []

N, BASE, EXPONENT, X, COEFFS = 5, 2, 10, 4, [1, 2, 3]


def expected():
  return {"n": N, "fact": 0, "base": BASE, "exp": EXPONENT, "pow": 0,
          "x": X, "y": 0, "coeffs": COEFFS, "deg": len(COEFFS)}
