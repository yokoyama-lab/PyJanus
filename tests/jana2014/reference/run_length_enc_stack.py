"""Run-length encoding between two stacks, reading the text from the top."""

from itertools import groupby

PUSHED = [12, 53, 53, 53, 32, 32]


def expected():
  text_top_first = list(reversed(PUSHED))
  runs = [(value, len(list(run))) for value, run in groupby(text_top_first)]
  arc_top_first = []
  for value, count in reversed(runs):
    arc_top_first += [count, value]
  return {"text": [], "arc": arc_top_first}
