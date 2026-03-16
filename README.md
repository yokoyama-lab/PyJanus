# PyJanus

A Python interpreter for **Janus**, the reversible programming language.

Janus is a simple imperative language in which every computation is
reversible: any program can be run both forwards and backwards.
PyJanus provides a complete interpreter, a debugger with forward/backward
stepping, a C++ code generator, and a set of analysis tools for
reversible-computing research.

## Quick Start

```bash
# Run a program
python3 -m jana_py.cli examples/fib.ja

# Invert a program (swap call/uncall, reverse statements)
python3 -m jana_py.cli -i examples/fib.ja

# Step-by-step debugger
python3 -m jana_py.cli -d examples/fib.ja

# Generate C++ code
python3 -m jana_py.cli -c examples/fib.ja
```

No external dependencies are required — only Python 3.10+.

## Language Features

| Feature | Syntax |
|---------|--------|
| Assignment | `x += expr`, `x -= expr`, `x ^= expr` |
| Swap | `x <=> y` |
| Conditional | `if cond then ... else ... fi cond` |
| Loop | `from cond do ... loop ... until cond` |
| Iteration | `iterate int i = a to b ... end` |
| Local scope | `local int x = e1 ... delocal int x = e2` |
| Procedures | `call proc(args)` / `uncall proc(args)` |
| Stack | `push(x, s)` / `pop(x, s)` |
| Output | `printf("%d", x)` / `show(x)` / `print("text")` |
| Struct | `struct Pair { int x, int y }` |
| Initializers | `Pair p = {1, 2}`, `int arr[] = {1, 2, 3}` |
| Preprocessor | `#define`, `#include`, `#ifdef` / `#endif` |
| Types | `int`, `i8`..`u64`, `bool`, `stack`, `char` |

## Analysis Tools

PyJanus includes five research modules for studying reversible computation:

```bash
# Synthesize a reversible gate network (CNOT, Toffoli, SWAP)
python3 -m jana_py.cli --circuit examples/fib.ja

# Profile space usage (pebble game analysis)
python3 -m jana_py.cli --profile examples/fib.ja

# Inverse interpreter: given output, find the input
python3 -m jana_py.cli --inverse '{"x": 10}' program.ja
```

| Module | File | Purpose |
|--------|------|---------|
| Bennett embedding | `jana_py/bennett.py` | Automatic reversibilization (compute-copy-uncompute) |
| Circuit synthesis | `jana_py/circuit.py` | Translate programs to reversible gate networks |
| Equivalence check | `jana_py/equiv.py` | Verify two programs compute the same function |
| Space profiler | `jana_py/pebble.py` | Track memory usage per step (Bennett's pebble game) |
| Inverse interpreter | `jana_py/inverse.py` | Compute initial state from final state |

## Examples

| File | Description |
|------|-------------|
| `fib.ja` | Recursive Fibonacci |
| `caesar.ja` | Reversible Caesar cipher (encrypt with `call`, decrypt with `uncall`) |
| `linked-list.ja` | Reversible linked list with struct array node pool |
| `sort-network.ja` | Reversible sorting network on struct arrays |
| `build-dict.ja` | Dictionary construction with macros and structs |
| `factor.ja` | Integer factorization |
| `sqrt.ja` | Integer square root |
| `run-length-enc.ja` | Run-length encoding |
| `stack-operations.ja` | Stack push/pop operations |

## Tests

```bash
python3 -m pytest tests/ -q
```

## References

- T. Yokoyama and R. Glueck. A reversible programming language and its
  invertible self-interpreter. In *Proc. PEPM*, pp. 144-153, ACM, 2007.
- C. H. Bennett. Logical reversibility of computation.
  *IBM Journal of Research and Development*, 17(6):525-532, 1973.

## License

BSD-3-Clause. See [LICENSE](LICENSE).
