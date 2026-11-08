"""Independent algorithm-level oracle for the sample, not a Janus translation."""
from bisect import bisect_left

VALUES = [-2, 0, 0, 4, 9]
KEY = 0
N = 5
GARBAGE = []

def expected():
  p = bisect_left(VALUES, KEY)
  first = p if p < N and VALUES[p] == KEY else N
  return {'a': VALUES[:], 'key': KEY, 'n': N, 'p': p,
          'f': 7 ^ int(KEY in VALUES), 'result': 7 ^ first}
