"""Knuth-Morris-Pratt: the failure function and the number of occurrences.
The prefix-length and branch logs are garbage."""

GARBAGE = ["gb", "gq"]

P = [1, 2, 1]
T = [1, 2, 1, 2, 1, 2, 1, 1, 2, 1]


def failure(pattern):
  table = [0] * len(pattern)
  k = 0
  for i in range(1, len(pattern)):
    while k and pattern[k] != pattern[i]:
      k = table[k - 1]
    if pattern[k] == pattern[i]:
      k += 1
    table[i] = k
  return table


def expected():
  m = len(P)
  count = sum(1 for i in range(len(T) - m + 1) if T[i:i + m] == P)
  return {"p": P, "t": T, "m": m, "n": len(T), "f": failure(P), "cnt": count}
