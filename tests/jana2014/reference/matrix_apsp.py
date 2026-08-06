"""All-pairs shortest paths by repeated min-plus squaring of the weight matrix.
The three 4x4 blocks are W, W^2 and W^4."""

GARBAGE = []

V = 4
INF = 10000
WEIGHTS = {(0, 1): 5, (0, 3): 10, (1, 2): 3, (2, 3): 1}
SQUARINGS = 2


def minplus(a, b):
  return [[min(a[i][k] + b[k][j] for k in range(V)) for j in range(V)] for i in range(V)]


def expected():
  w = [[0 if i == j else INF for j in range(V)] for i in range(V)]
  for (u, v), weight in WEIGHTS.items():
    w[u][v] = weight
  blocks, current = [w], w
  for _ in range(SQUARINGS):
    current = minplus(current, current)
    blocks.append(current)
  return {"v_n": V, "t_n": SQUARINGS, "inf": INF,
          "m_arr": [cell for block in blocks for row in block for cell in row]}
