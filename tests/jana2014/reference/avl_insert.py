"""AVL insertion of 1..7 in order. The rotation and overwrite logs are garbage."""

from _avl import Avl

KEYS = [1, 2, 3, 4, 5, 6, 7]
NODES = 8


def expected():
  tree = Avl(NODES)
  for key in KEYS:
    tree.insert(key)
  return tree.arrays()
