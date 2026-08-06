"""Three ways to write Fibonacci reversibly, on the same n.

`fib` consumes n and leaves the pair; `fiba` preserves n and leaves F(n+1) in a
single result; `fibb` consumes n and leaves F(n+1). Convention: F(1)=F(2)=1.
"""

N = 4


def fibonacci(k):
  a, b = 1, 1
  for _ in range(k - 1):
    a, b = b, a + b
  return a


def expected():
  return {
    "n": 0, "x1": fibonacci(N + 1), "x2": fibonacci(N + 2),
    "an": N, "ar": fibonacci(N + 1), "ax1": 0, "ax2": 0,
    "bn": 0, "br": fibonacci(N + 1), "bx1": 0, "bx2": 0,
  }
