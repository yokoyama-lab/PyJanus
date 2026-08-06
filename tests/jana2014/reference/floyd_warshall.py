"""Floyd-Warshall all-pairs shortest paths, in place on the distance matrix."""

V = 4
INF = 10000
WEIGHTS = {(0, 1): 5, (0, 3): 10, (1, 2): 3, (2, 3): 1}


def expected():
  path = [[0 if i == j else INF for j in range(V)] for i in range(V)]
  for (u, v), w in WEIGHTS.items():
    path[u][v] = w
  for k in range(V):
    for i in range(V):
      for j in range(V):
        if path[i][k] + path[k][j] < path[i][j]:
          path[i][j] = path[i][k] + path[k][j]
  return {"v_n": V, "inf": INF, "path": [cell for row in path for cell in row]}
