"""An array of structs passed to a procedure that bumps each value and copies
the new value into the tag field."""

VALUES = [10, 20, 30]


def expected():
  return {"n": len(VALUES),
          "data": [{"v": v + 1, "tag": v + 1} for v in VALUES]}
