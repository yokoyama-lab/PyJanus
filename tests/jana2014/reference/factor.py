"""Prime factorisation in ascending order; the input is consumed to zero."""

NUM, WIDTH = 840, 20


def expected():
  factors, n, d = [], NUM, 2
  while d * d <= n:
    while n % d == 0:
      factors.append(d)
      n //= d
    d += 1
  if n > 1:
    factors.append(n)
  # fact[0] is left unused by the program; the factors start at index 1.
  table = [0] + factors + [0] * (WIDTH - 1 - len(factors))
  return {"num": 0, "fact": table}
