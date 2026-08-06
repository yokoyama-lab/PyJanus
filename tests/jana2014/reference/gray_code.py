"""Binary -> reflected Gray code, bit 0 least significant."""

GARBAGE = []

BITS = [0, 1, 0, 1]


def to_int(bits):
  return sum(bit << i for i, bit in enumerate(bits))


def to_bits(value, width):
  return [(value >> i) & 1 for i in range(width)]


def expected():
  value = to_int(BITS)
  return {"bits": to_bits(value ^ (value >> 1), len(BITS))}
