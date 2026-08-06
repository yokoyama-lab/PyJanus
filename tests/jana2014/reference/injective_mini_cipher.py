"""A three-round modular cipher, encrypted then decrypted."""

L, R, K0, K1, K2, M = 100, 42, 200, 150, 91, 256


def expected():
  return {"L": L, "R": R, "K0": K0, "K1": K1, "K2": K2, "m": M, "logs": [0, 0, 0]}
