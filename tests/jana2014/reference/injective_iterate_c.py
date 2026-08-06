"""Four uses of `iterate`: a prefix sum (undone), an xor chain, an odd-even
swap, and a Feistel block (undone)."""

GARBAGE = []

A = [1, 2, 3, 4, 5]
B = [5, 3, 6, 2, 7]
C = [10, 20, 30, 40, 50, 60]
L, R, KEY, ROUNDS = 5, 7, 3, 4


def xor_chain(values):
  out = list(values)
  for i in range(1, len(out)):
    out[i] ^= out[i - 1]
  return out


def odd_even_swap(values):
  out = list(values)
  for i in range(0, len(out) - 1, 2):
    out[i], out[i + 1] = out[i + 1], out[i]
  return out


def expected():
  return {"a": A, "b": xor_chain(B), "c": odd_even_swap(C),
          "n5": len(A), "n6": len(C), "L": L, "R": R, "K": KEY, "rounds": ROUNDS}
