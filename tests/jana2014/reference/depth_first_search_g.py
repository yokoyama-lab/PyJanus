"""Depth-first search on a directed graph: preorder visit sequence.
The recursion-decision log `blog` is garbage."""

GARBAGE = ["blog"]

V = 5
EDGES = [(0, 1), (0, 2), (1, 3), (2, 3), (3, 4)]


def expected():
  matrix = [[0] * V for _ in range(V)]
  for u, v in EDGES:
    matrix[u][v] = 1
  visited = [0] * V
  order = []

  def visit(u):
    visited[u] = 1
    order.append(u)
    for v in range(V):
      if matrix[u][v] and not visited[v]:
        visit(v)

  visit(0)
  return {
    "adj": [cell for row in matrix for cell in row],
    "v_n": V, "visited": visited,
    "order": order + [0] * (V - len(order)), "cnt": len(order),
  }
