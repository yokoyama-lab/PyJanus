"""A staircase of injective integer functions, applied in sequence.

inc, neg, add (into the second argument), dbl, mul_const, mul, square, and the
Cantor pairing in the file's own convention pi(a,b) = (a+b)(a+b+1)/2 + a.
"""

GARBAGE = []

X0, Y0, N, A, B, CA, CB = 5, 10, 3, 4, 7, 3, 4


def expected():
  x = -(X0 + 1)                       # inc then neg
  y = ((Y0 + x) * 2) * N              # add, dbl, mul_const
  return {"x": x, "y": y, "n": N, "a": A, "b": B, "c": A * B, "sq": x * x,
          "ca": CA, "cb": CB, "z": (CA + CB) * (CA + CB + 1) // 2 + CA}
