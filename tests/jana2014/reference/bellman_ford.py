"""Bellman-Ford with negative weights: distances and the predecessor tree.
The overwritten-value and decision logs are garbage."""

V = 5
INF = 10000
EDGES = [(0, 1, 6), (0, 3, 7), (1, 2, 5), (1, 3, 8), (1, 4, -4),
         (2, 1, -2), (3, 2, -3), (3, 4, 9), (4, 0, 2), (4, 2, 7)]


def expected():
  dist = [0] + [INF] * (V - 1)
  pred = [-1] * V
  for _ in range(V - 1):
    for u, v, w in EDGES:
      if dist[u] + w < dist[v]:
        dist[v] = dist[u] + w
        pred[v] = u
  return {
    "v_n": V, "e_n": len(EDGES), "inf": INF, "dist": dist, "pred": pred,
    "eu": [e[0] for e in EDGES], "ev": [e[1] for e in EDGES], "ew": [e[2] for e in EDGES],
  }
