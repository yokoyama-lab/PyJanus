"""Run-length encoding into (value, count) pairs; the input is consumed."""

from itertools import groupby

TEXT = [1, 1, 2, 2, 2, 1]
TEXT_WIDTH, ARC_WIDTH = 7, 14


def expected():
  pairs = []
  for value, run in groupby(TEXT):
    pairs += [value, len(list(run))]
  return {
    "text": [0] * TEXT_WIDTH,
    "arc": pairs + [0] * (ARC_WIDTH - len(pairs)),
  }
