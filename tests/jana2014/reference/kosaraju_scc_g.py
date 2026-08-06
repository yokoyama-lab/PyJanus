"""Kosaraju's strongly connected components: finish order, then components on
the transpose. The recursion log is garbage."""

GARBAGE = ["blog"]

V = 5
EDGES = [(0, 1), (1, 2), (2, 0), (2, 3), (3, 4), (4, 3)]


def expected():
  graph = [[0] * V for _ in range(V)]
  transpose = [[0] * V for _ in range(V)]
  for u, v in EDGES:
    graph[u][v] = 1
    transpose[v][u] = 1

  visited = [0] * V
  finish = []

  def first_pass(u):
    visited[u] = 1
    for v in range(V):
      if graph[u][v] and not visited[v]:
        first_pass(v)
    finish.append(u)

  for u in range(V):
    if not visited[u]:
      first_pass(u)

  comp = [0] * V
  label = 0

  def second_pass(u):
    comp[u] = label
    for v in range(V):
      if transpose[u][v] and not comp[v]:
        second_pass(v)

  for u in reversed(finish):
    if not comp[u]:
      label += 1
      second_pass(u)

  return {
    "adj": [cell for row in graph for cell in row],
    "adjt": [cell for row in transpose for cell in row],
    "v_n": V, "visited": visited, "order": finish, "comp": comp, "ncomp": label,
  }
