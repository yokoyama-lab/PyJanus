"""Passing a scalar and an array element to the same incrementing procedure."""

INT, ARRAY = 4, [42, 17]


def expected():
  return {"test_int": INT + 1, "test_array": [ARRAY[0] + 1, ARRAY[1]]}
