"""`local struct` copies a struct in and checks it back out unchanged, so the
loop can read fields without disturbing the array."""

GARBAGE = []

OUT = [{"dist": 3, "len": 2, "next": 9}, {"dist": 7, "len": 5, "next": 7}]


def expected():
  total = sum(entry["dist"] + entry["len"] + entry["next"] for entry in OUT)
  return {"out": OUT, "s": total}
