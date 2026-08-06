"""AVL insertion of 1..7, then deletion of 4 (the root, with two children, so
its successor's key moves up). The logs are garbage."""

from _avl import Avl

KEYS = [1, 2, 3, 4, 5, 6, 7]
REMOVE = 4
NODES = 8


def expected():
  tree = Avl(NODES)
  for key in KEYS:
    tree.insert(key)
  tree.delete(REMOVE)
  return tree.arrays()
