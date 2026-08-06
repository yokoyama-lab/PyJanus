"""Landauer embedding of a four-instruction irreversible language.

  1  a := b        destructive, so the overwritten a is traced
  2  b := a        destructive, so the overwritten b is traced
  3  a := (a+1) mod 4     reversible, traces 0
  _  swap a, b            reversible, traces 0
"""

PROGRAM = [1, 3, 2]
A0, B0 = 2, 1


def expected():
  a, b, trace = A0, B0, []
  for op in PROGRAM:
    if op == 1:
      trace.append(a)
      a = b
    elif op == 2:
      trace.append(b)
      b = a
    elif op == 3:
      trace.append(0)
      a = (a + 1) % 4
    else:
      trace.append(0)
      a, b = b, a
  return {"p": PROGRAM, "L": len(PROGRAM), "a": a, "b": b, "tr": trace}
