"""Prim's minimum spanning tree: final keys, parents and total weight."""

GARBAGE = ["blog", "dlog"]

V = 5
INF = 100000
EDGES = {(0, 1): 2, (0, 3): 6, (1, 2): 3, (1, 3): 8, (1, 4): 5, (2, 4): 7, (3, 4): 9}


def expected():
  w = [[0] * V for _ in range(V)]
  for (u, v), weight in EDGES.items():
    w[u][v] = w[v][u] = weight
  key = [0] + [INF] * (V - 1)
  parent = [-1] * V
  intree = [0] * V
  for _ in range(V):
    u = min((key[i], i) for i in range(V) if not intree[i])[1]
    intree[u] = 1
    for v in range(V):
      if w[u][v] and not intree[v] and w[u][v] < key[v]:
        key[v] = w[u][v]
        parent[v] = u
  return {
    "w": [cell for row in w for cell in row], "v_n": V, "inf": INF,
    "key": key, "parent": parent, "intree": intree, "total": sum(key),
  }
