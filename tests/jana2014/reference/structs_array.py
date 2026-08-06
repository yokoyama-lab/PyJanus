"""An array of structs: cross-element field reads, then a swap between them."""


def expected():
  v = [{"a": 1, "b": 2}, {"a": 3, "b": 4}, {"a": 5, "b": 0}]
  v[2]["b"] += v[0]["a"] + v[1]["b"]
  v[0]["a"], v[1]["b"] = v[1]["b"], v[0]["a"]
  return {"v": v}
