"""Free fall in integer steps: each tick the body gains g of speed and falls the
average of its speed before and after (g*t + g/2). Run forwards for t_end
ticks, then run backwards from a different state."""

G, H0, T_END = 10, 176, 3
T_BACK, V_BACK, T_END_BACK = 4, 40, 4


def drop(ticks):
  return sum(G * t + G // 2 for t in range(ticks))


def expected():
  return {"g": G, "t": T_END, "v": G * T_END, "h": H0 - drop(T_END), "t_end": T_END,
          "t_r": 0, "v_r": 0, "h_r": drop(T_END_BACK), "t_end_r": T_END_BACK}
