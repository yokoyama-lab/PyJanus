"""Topological sort of a DAG, left as the DFS post-order (reverse it to read
the topological order). The recursion log is garbage."""

V = 5
EDGES = [(0, 1), (0, 2), (1, 3), (2, 3), (3, 4)]


def expected():
  matrix = [[0] * V for _ in range(V)]
  for u, v in EDGES:
    matrix[u][v] = 1
  visited = [0] * V
  post = []

  def visit(u):
    visited[u] = 1
    for v in range(V):
      if matrix[u][v] and not visited[v]:
        visit(v)
    post.append(u)

  for u in range(V):
    if not visited[u]:
      visit(u)
  return {"adj": [cell for row in matrix for cell in row],
          "v_n": V, "visited": visited, "order": post}
