"""Breadth-first search on an undirected graph: layer distances and visit order.
The discovery-decision log `blog` is garbage."""

GARBAGE = ["blog"]

V = 6
EDGES = [(0, 1), (0, 2), (1, 3), (2, 3), (3, 4), (4, 5)]
SRC = 0


def adjacency():
  matrix = [[0] * V for _ in range(V)]
  for u, v in EDGES:
    matrix[u][v] = matrix[v][u] = 1
  return matrix


def expected():
  matrix = adjacency()
  dist = [0] * V
  visited = [0] * V
  order = [SRC]
  visited[SRC] = 1
  head = 0
  while head < len(order):
    u = order[head]
    head += 1
    for v in range(V):
      if matrix[u][v] and not visited[v]:
        visited[v] = 1
        dist[v] = dist[u] + 1
        order.append(v)
  return {
    "adj": [cell for row in matrix for cell in row],
    "v_n": V, "src": SRC, "dist": dist, "visited": visited,
    "queue": order, "head": len(order), "tail": len(order),
  }
