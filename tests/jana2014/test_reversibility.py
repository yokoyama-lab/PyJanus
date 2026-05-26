"""Verify that call+uncall is the identity for various statement patterns.

Each test defines a procedure and checks that call(proc); uncall(proc)
returns all variables to their pre-call values.
"""
from __future__ import annotations

from pathlib import Path
import sys
import textwrap
import unittest
import copy

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from jana_py.parser import parse_program
from jana_py.validate import validate_program
from jana_py.runtime import Runtime


def run_and_get_store(source: str) -> dict[str, object]:
  """Run a program and return the final store as {name: value}."""
  program = parse_program("rev_test.ja", textwrap.dedent(source))
  validate_program(program)
  rt = Runtime(program)
  rt.run()
  assert rt._root_frame is not None
  return {k: copy.deepcopy(c.value) for k, c in rt._root_frame.vars.items()}


class ReversibilityTests(unittest.TestCase):

  def assertRoundTrip(self, proc_source: str, main_vars: str, call_args: str) -> None:
    """Assert call+uncall restores variables to initial values."""
    # Program with call only
    fwd_source = f"""\
      {proc_source}

      procedure main()
          {main_vars}
          call {call_args}
      """
    # Program with call + uncall
    rt_source = f"""\
      {proc_source}

      procedure main()
          {main_vars}
          call {call_args}
          uncall {call_args}
      """
    fwd_store = run_and_get_store(fwd_source)
    rt_store = run_and_get_store(rt_source)
    # After call+uncall, every var should equal its initial value (= rt_store without call)
    init_source = f"""\
      {proc_source}

      procedure main()
          {main_vars}
          skip
      """
    init_store = run_and_get_store(init_source)
    self.assertEqual(rt_store, init_store, f"call+uncall did not restore initial state")

  def test_assign(self) -> None:
    self.assertRoundTrip(
      "procedure add(int x, int y)\n    x += y",
      "int a = 3\n    int b = 5",
      "add(a, b)",
    )

  def test_swap(self) -> None:
    self.assertRoundTrip(
      "procedure do_swap(int x, int y)\n    x <=> y",
      "int a = 3\n    int b = 5",
      "do_swap(a, b)",
    )

  def test_if_then_else(self) -> None:
    self.assertRoundTrip(
      "procedure branch(int x, int flag)\n"
      "    if flag = 1 then\n"
      "        x += 10\n"
      "    else\n"
      "        x += 20\n"
      "    fi flag = 1",
      "int x = 5\n    int flag = 1",
      "branch(x, flag)",
    )

  def test_from_loop(self) -> None:
    self.assertRoundTrip(
      "procedure count_up(int x, int n)\n"
      "    from n = 0 loop\n"
      "        n += 1\n"
      "        x += n\n"
      "    until n = 5",
      "int x\n    int n",
      "count_up(x, n)",
    )

  def test_iterate(self) -> None:
    self.assertRoundTrip(
      "procedure fill(int arr[5])\n"
      "    iterate int i = 0 to 4\n"
      "        arr[i] += i * i\n"
      "    end",
      "int arr[5]",
      "fill(arr)",
    )

  def test_local(self) -> None:
    self.assertRoundTrip(
      "procedure double(int x)\n"
      "    local int tmp = x\n"
      "        x += tmp\n"
      "    delocal int tmp = x / 2",
      "int x = 7",
      "double(x)",
    )

  def test_push_pop(self) -> None:
    self.assertRoundTrip(
      "procedure build_stack(stack s, int a, int b)\n"
      "    push(a, s)\n"
      "    push(b, s)",
      "stack s\n    int a = 10\n    int b = 20",
      "build_stack(s, a, b)",
    )

  def test_nested_calls(self) -> None:
    self.assertRoundTrip(
      "procedure inner(int x)\n"
      "    x += 1\n\n"
      "procedure outer(int x)\n"
      "    call inner(x)\n"
      "    x += 10\n"
      "    call inner(x)",
      "int x",
      "outer(x)",
    )

  def test_recursive_fib(self) -> None:
    self.assertRoundTrip(
      "procedure fib(int x1, int x2, int n)\n"
      "    if n = 0 then\n"
      "        x1 += 1\n"
      "        x2 += 1\n"
      "    else\n"
      "        n -= 1\n"
      "        call fib(x1, x2, n)\n"
      "        x1 += x2\n"
      "        x1 <=> x2\n"
      "    fi x1 = x2",
      "int x1\n    int x2\n    int n = 5",
      "fib(x1, x2, n)",
    )

  def test_struct_fields(self) -> None:
    self.assertRoundTrip(
      "struct Pair { int x, int y }\n\n"
      "procedure bump(Pair p)\n"
      "    p.x += 1\n"
      "    p.y += 2",
      "Pair p",
      "bump(p)",
    )

  def test_struct_array(self) -> None:
    self.assertRoundTrip(
      "struct Pair { int x, int y }\n\n"
      "procedure fill(Pair ps[3])\n"
      "    ps[0].x += 10\n"
      "    ps[1].y += 20\n"
      "    ps[2].x += 30",
      "Pair ps[3]",
      "fill(ps)",
    )

  def test_xor_swap(self) -> None:
    self.assertRoundTrip(
      "procedure xor_swap(int a, int b)\n"
      "    a ^= b\n"
      "    b ^= a\n"
      "    a ^= b",
      "int a = 42\n    int b = 17",
      "xor_swap(a, b)",
    )

  def test_array_with_loop(self) -> None:
    self.assertRoundTrip(
      "procedure sum_into(int arr[4], int total)\n"
      "    iterate int i = 0 to 3\n"
      "        total += arr[i]\n"
      "    end",
      "int arr[4]\n    int total\n"
      "    arr[0] += 1\n    arr[1] += 2\n    arr[2] += 3\n    arr[3] += 4",
      "sum_into(arr, total)",
    )


if __name__ == "__main__":
  unittest.main()
