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
python3 -m jana_py.cli --std jana2014 tests/jana2014/fixtures/examples/fib.ja

# Invert a program (swap call/uncall, reverse statements)
python3 -m jana_py.cli --std jana2014 -i tests/jana2014/fixtures/examples/fib.ja

# Step-by-step debugger
python3 -m jana_py.cli --std jana2014 -d tests/jana2014/fixtures/examples/fib.ja

# Generate C++ code
python3 -m jana_py.cli --std jana2014 -c tests/jana2014/fixtures/examples/fib.ja
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

## Standard Library

PyJanus ships a small **reversible standard library** (it installs with the
package). Every procedure is reversible — `uncall` undoes `call` exactly:

```janus
#include "std/array.ja"

void main() {
    int a[5] = {10, 20, 30, 40, 50};
    call reverse(a, 5);     // a = {50, 40, 30, 20, 10}
    uncall reverse(a, 5);   // a = {10, 20, 30, 40, 50}
}
```

`#include "std/..."` resolves through the preprocessor's search path: relative
to the including file first, then any `-I DIR` (repeatable), then the bundled
library. So the include above works from any directory.

| Module | Procedures |
|--------|------------|
| `std/array.ja` | `reverse`, `rotate_left`, `xor_into`, `add_into`, `cswap` |
| `std/bits.ja` | `flip_bit`, `swap_bits`, `bit_reverse`, `rotate_bits_left` |
| `std/math.ja` | `mul_acc`, `divmod`, `gcd` (reversible Euclid with a quotient stack) |
| `std/reduce.ja` | `sum_into`, `dot_into`, `count_into`, `min_into`, `max_into` |
| `std/sort.ja` | `sort` (reversible bubble sort, recording swap decisions) |
| `std/stack.ja` | `copy_top`, `move_all` |

Two reversibility patterns recur in the library and are worth knowing:

- **Ancilla flags.** A value-only comparator (`if x > y ... fi x < y`) breaks its
  reversibility assertion on an already-ordered pair, so `cswap` and `sort`
  record each swap decision in an extra flag bit.
- **History.** Operations that discard information (`gcd`, `min_into`, `sort`)
  are made reversible by keeping just enough history — a quotient stack, a flag
  array, a stack of deltas — for `uncall` to replay them backwards.

## Analysis Tools

PyJanus includes five research modules for studying reversible computation:

```bash
# Synthesize a reversible gate network (CNOT, Toffoli, SWAP)
python3 -m jana_py.cli --std jana2014 --circuit tests/jana2014/fixtures/examples/fib.ja

# Profile space usage (pebble game analysis)
python3 -m jana_py.cli --std jana2014 --profile tests/jana2014/fixtures/examples/fib.ja

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

## Example Fixtures

Example programs live under dialect-specific test fixtures:

- `tests/jana2014/fixtures/examples/`
- `tests/jana2014_in_out/fixtures/examples/`
- `tests/jana2014basic/fixtures/examples/`
- `tests/janus1982ext/fixtures/examples/`
- `tests/janus2026/fixtures/examples/`

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
