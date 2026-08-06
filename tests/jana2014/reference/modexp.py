"""Modular exponentiation by repeated squaring. The running power `p` and the
overwrite log are garbage."""

BASE, EXPONENT, MODULUS = 7, 133, 31


def expected():
  return {"base": BASE, "e": EXPONENT, "m": MODULUS, "pw": 0,
          "r": pow(BASE, EXPONENT, MODULUS)}
