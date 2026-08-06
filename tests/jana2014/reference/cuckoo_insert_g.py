"""Cuckoo hashing with an eviction chain over two tables.

h1(x) = x mod 4 and h2(x) = (x div 4 + x) mod 4. A key displaces whatever sits
in its slot; the displaced key is re-homed in the other table, and so on until
an empty slot absorbs the chain. `tr` records the evicted keys, `m` their count.
"""

GARBAGE = ["tr", "m"]

T1 = [0, 0, 2, 3]
T2 = [0, 0, 5, 0]
KEY = 6
TRACE_WIDTH = 3


def expected():
  t1, t2 = list(T1), list(T2)
  current, in_first, evicted = KEY, True, []
  while current:
    table = t1 if in_first else t2
    slot = current % 4 if in_first else (current // 4 + current) % 4
    current, table[slot] = table[slot], current
    if current:
      evicted.append(current)
    in_first = not in_first
  return {"t1": t1, "t2": t2, "k": KEY, "m": len(evicted),
          "tr": evicted + [0] * (TRACE_WIDTH - len(evicted))}
