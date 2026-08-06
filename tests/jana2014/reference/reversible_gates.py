"""Fredkin (controlled swap) applied elementwise, then one Toffoli."""

CTRL = [1, 0, 1, 0]
P = [5, 6, 7, 8]
Q = [50, 60, 70, 80]


def expected():
  ctrl, p, q = list(CTRL), list(P), list(Q)
  for i, control in enumerate(ctrl):
    if control:
      p[i], q[i] = q[i], p[i]
  ctrl[3] ^= ctrl[0] & ctrl[2]
  return {"ctrl": ctrl, "p": p, "q": q}
