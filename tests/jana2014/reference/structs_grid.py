"""A 2-D array of structs, read across cells."""


def expected():
  grid = [[{"x": 0, "y": 0} for _ in range(2)] for _ in range(2)]
  grid[0][0]["x"] += 1
  grid[0][1]["y"] += 2
  grid[1][0]["x"] += 3
  grid[1][1]["y"] += 4
  grid[0][0]["y"] += grid[1][1]["y"]
  return {"grid": grid}
