"""Tree sort: insert into an AVL that counts multiplicities, then read it out
in order. Nodes are allocated on first occurrence of a key."""

from _avl import Avl

A = [3, 1, 2, 3, 1, 3]
NODES = 7


def expected():
  tree = Avl(NODES)
  counts = [0] * NODES
  for value in A:
    node = tree.root
    while node and tree.key[node] != value:
      node = tree.left[node] if value < tree.key[node] else tree.right[node]
    if node:
      counts[node] += 1
    else:
      allocated = tree.nfree
      tree.insert(value)
      counts[allocated] = 1
  arrays = tree.arrays()
  arrays.update({"a": A, "n": len(A), "b": sorted(A), "cnt": counts})
  return arrays
