"""Positional digits of N in base B, least significant first."""

N, B, WIDTH = 2026, 10, 4


def expected():
  digits = [(N // B ** i) % B for i in range(WIDTH)]
  return {"n": N, "b": B, "d": digits}
