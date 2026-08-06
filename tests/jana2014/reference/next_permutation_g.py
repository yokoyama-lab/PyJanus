"""Next permutation in lexicographic order. The overwrite log is garbage."""

GARBAGE = ["glog"]

D = [6, 7, 3, 5, 4, 2, 1, 0]


def expected():
  d = list(D)
  i = len(d) - 2
  while i >= 0 and d[i] >= d[i + 1]:
    i -= 1
  j = len(d) - 1
  while d[j] <= d[i]:
    j -= 1
  d[i], d[j] = d[j], d[i]
  d[i + 1:] = reversed(d[i + 1:])
  return {"d": d, "n": len(D)}
