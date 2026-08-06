"""Search in a fixed AVL tree: found returns the key, absent returns 0."""

GARBAGE = []

KEY = [-999, 1, 2, 3, 4, 5, 6, 7]
LEFT = [0, 0, 1, 0, 2, 0, 5, 0]
RIGHT = [0, 0, 3, 0, 6, 0, 7, 0]
ROOT = 4


def search(target):
  node = ROOT
  while node != 0:
    if KEY[node] == target:
      return KEY[node]
    node = LEFT[node] if target < KEY[node] else RIGHT[node]
  return 0


def expected():
  return {"key": KEY, "left": LEFT, "right": RIGHT, "root": ROOT,
          "res5": search(5), "res8": search(8)}
