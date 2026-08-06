"""Dijkstra's shortest paths from vertex 0 on a weighted digraph.
The overwritten-distance and decision logs are garbage."""

V = 5
INF = 100000
WEIGHTS = {(0, 1): 10, (0, 3): 5, (1, 2): 1, (3, 1): 3,
           (3, 2): 9, (3, 4): 2, (4, 2): 6, (2, 4): 4}


def expected():
  matrix = [[0] * V for _ in range(V)]
  for (u, v), w in WEIGHTS.items():
    matrix[u][v] = w
  dist = [0] + [INF] * (V - 1)
  visited = [0] * V
  for _ in range(V):
    u = min((d, i) for i, d in enumerate(dist) if not visited[i])[1]
    visited[u] = 1
    for v in range(V):
      if matrix[u][v] and dist[u] + matrix[u][v] < dist[v]:
        dist[v] = dist[u] + matrix[u][v]
  return {
    "w": [cell for row in matrix for cell in row],
    "v_n": V, "inf": INF, "dist": dist, "visited": visited,
  }
