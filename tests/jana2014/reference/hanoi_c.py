"""Towers of Hanoi: move a tower of n disks between three stacks.

The recursion branches on n alone, so no decision has to be recorded and the
inverse is the same tree walked backwards. `moves` is 2^n - 1, determined by n
rather than needed to invert anything.
"""

GARBAGE = []

DISKS = 3


def expected():
  pegs: dict[str, list[int]] = {"a": list(range(DISKS, 0, -1)), "b": [], "c": []}

  def hanoi(n, src, dst, via):
    if n == 0:
      return 0
    moved = hanoi(n - 1, src, via, dst)
    pegs[dst].append(pegs[src].pop())
    return moved + 1 + hanoi(n - 1, via, dst, src)

  moves = hanoi(DISKS, "a", "c", "b")
  # Stacks read top first; a Python list holds the bottom first.
  return {"a": pegs["a"][::-1], "b": pegs["b"][::-1], "c": pegs["c"][::-1],
          "n": DISKS, "moves": moves}
