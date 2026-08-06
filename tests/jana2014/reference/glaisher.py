"""Glaisher's bijection: partitions into odd parts <-> partitions into distinct
parts. A part 2i+1 with multiplicity m contributes (2i+1)*2^k for each bit k
set in m. odd[i] counts part 2i+1; dist[j] flags part j+1."""

GARBAGE = []

ODD = [3, 0, 1, 0, 0, 0]
DIST_WIDTH = 12


def expected():
  distinct = [0] * DIST_WIDTH
  for i, multiplicity in enumerate(ODD):
    part = 2 * i + 1
    bit = 0
    while multiplicity:
      if multiplicity & 1:
        distinct[part * 2 ** bit - 1] = 1
      multiplicity >>= 1
      bit += 1
  return {"odd": [0] * len(ODD), "dist": distinct}
