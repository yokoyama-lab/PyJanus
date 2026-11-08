"""Independent algorithm-level oracle for the sample, not a Janus translation."""

VALUES = [4, -1, 4, 8, 4, 11]
KEY = 4
N = 5
GARBAGE = []

def expected():
  first = next((i for i, value in enumerate(VALUES[:N]) if value == KEY), N)
  answer = {'a': VALUES[:], 'key': KEY, 'n': N, 'p': first, 'f': 7 ^ int(KEY in VALUES[:N])}
  return answer
