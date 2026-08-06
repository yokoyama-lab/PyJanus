"""A struct passed through one procedure into another: the inner call adds
v[0] + w, the outer then adds v[1]."""


def expected():
  a = {"v": [10, 20, 30], "w": 5}
  return {"a": a, "r": a["v"][0] + a["w"] + a["v"][1]}
