"""A four-round Feistel cipher with an S-box, encrypted then decrypted, and the
key schedule uncalled away."""

GARBAGE = []

L, R, MASTER_KEY, ROUNDS = 5, 10, 6, 4
SBOX = [12, 5, 6, 11, 9, 0, 10, 13, 3, 14, 15, 8, 4, 7, 1, 2]
INV_SBOX = [5, 14, 15, 8, 12, 1, 2, 13, 11, 4, 6, 3, 0, 7, 9, 10]


def expected():
  # The S-boxes are declared inverse to each other; that is checkable here.
  assert all(INV_SBOX[SBOX[i]] == i for i in range(len(SBOX)))
  return {"L": L, "R": R, "master_key": MASTER_KEY, "rounds": ROUNDS,
          "rk": [0, 0, 0, 0], "sbox": SBOX, "inv_sbox": INV_SBOX}
