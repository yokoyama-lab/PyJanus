"""Binary search returning the lower bound: how many entries are below the key.

The answer is built one bit at a time from the widest probe down, so the
recorded decision bits are, read in that order, the binary digits of the answer
itself -- which is what makes them avoidable garbage rather than necessary
history. A version that uncomputed them would leave nothing behind.
"""

GARBAGE = ["flags"]

A = [2, 3, 5, 7, 11, 13, 17, 19]
KEY = 13
WIDTHS = [4, 2, 1]


def expected():
  index = 0
  for width in WIDTHS:
    if A[index + width - 1] < KEY:
      index += width
  return {"a": A, "key": KEY, "idx": index}
