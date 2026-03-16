from __future__ import annotations

from pathlib import Path
import sys
import textwrap
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from jana_py.parser import parse_program
from jana_py.runtime import Runtime
from jana_py.validate import validate_program


class StructRuntimeTests(unittest.TestCase):
  def runtime_for(self, source: str) -> Runtime:
    program = parse_program("struct_runtime.ja", textwrap.dedent(source))
    validate_program(program)
    return Runtime(program)

  def test_struct_variable_initializes_named_fields(self) -> None:
    runtime = self.runtime_for(
      """\
      struct Pair {
          int x,
          int y
      }

      procedure main()
          Pair p
          skip
      """
    )
    runtime.run()
    assert runtime._root_frame is not None
    cell = runtime._root_frame.vars["p"]
    self.assertEqual(cell.kind, "struct")
    self.assertEqual(cell.struct_name, "Pair")
    self.assertEqual(cell.value, {"x": 0, "y": 0})

  def test_struct_variable_persists_bool_and_stack_fields(self) -> None:
    runtime = self.runtime_for(
      """\
      struct Mixed {
          bool flag,
          stack xs
      }

      procedure main()
          Mixed m
          skip
      """
    )
    runtime.run()
    assert runtime._root_frame is not None
    cell = runtime._root_frame.vars["m"]
    self.assertEqual(cell.kind, "struct")
    self.assertEqual(cell.value, {"flag": False, "xs": []})

  def test_struct_field_update_and_read_behave_like_lvalues(self) -> None:
    runtime = self.runtime_for(
      """\
      struct Pair {
          int x,
          int y
      }

      procedure main()
          Pair p
          int z
          p.x += 1
          p.y += 2
          z += p.y
      """
    )
    runtime.run()
    assert runtime._root_frame is not None
    self.assertEqual(runtime._root_frame.vars["p"].value, {"x": 1, "y": 2})
    self.assertEqual(runtime._root_frame.vars["z"].value, 2)

  def test_struct_argument_updates_are_visible_to_caller(self) -> None:
    runtime = self.runtime_for(
      """\
      struct Pair {
          int x,
          int y
      }

      procedure bump(Pair p)
          p.x += 1
          p.y += 2

      procedure main()
          Pair p
          call bump(p)
      """
    )
    runtime.run()
    assert runtime._root_frame is not None
    self.assertEqual(runtime._root_frame.vars["p"].value, {"x": 1, "y": 2})

  def test_index_then_field_selector_chain_works(self) -> None:
    runtime = self.runtime_for(
      """\
      struct Entry {
          int k
      }

      procedure main()
          int di = 1
          int z
          Entry xs[2]
          xs[1].k += 6
          z += xs[di].k
      """
    )
    runtime.run()
    assert runtime._root_frame is not None
    self.assertEqual(runtime._root_frame.vars["di"].value, 1)
    self.assertEqual(runtime._root_frame.vars["z"].value, 6)
    self.assertEqual(runtime._root_frame.vars["xs"].value, [{"k": 0}, {"k": 6}])

  def test_struct_field_array_selector_chain_works(self) -> None:
    runtime = self.runtime_for(
      """\
      struct Entry {
          int k
      }

      struct Dict {
          int size,
          Entry entries[3]
      }

      procedure main()
          Dict d
          int i = 1
          int z
          d.size += 3
          d.entries[1].k += 6
          z += d.entries[i].k
      """
    )
    runtime.run()
    assert runtime._root_frame is not None
    self.assertEqual(runtime._root_frame.vars["z"].value, 6)
    self.assertEqual(runtime._root_frame.vars["d"].value["size"], 3)
    self.assertEqual(runtime._root_frame.vars["d"].value["entries"], [{"k": 0}, {"k": 6}, {"k": 0}])

  def test_struct_array_dims_before_name_works(self) -> None:
    runtime = self.runtime_for(
      """\
      struct Pair {
          int x,
          int y
      }

      procedure main()
          Pair[3] ps
          ps[0].x += 10
          ps[1].y += 20
          ps[2].x += 30
      """
    )
    runtime.run()
    assert runtime._root_frame is not None
    cell = runtime._root_frame.vars["ps"]
    self.assertEqual(cell.kind, "array")
    self.assertEqual(cell.shape, [3])
    self.assertEqual(cell.elem_struct_name, "Pair")
    self.assertEqual(cell.value, [{"x": 10, "y": 0}, {"x": 0, "y": 20}, {"x": 30, "y": 0}])

  def test_struct_2d_array_access(self) -> None:
    runtime = self.runtime_for(
      """\
      struct Pair {
          int x,
          int y
      }

      procedure main()
          Pair[2][2] ps
          ps[0][1].x += 5
          ps[1][0].y += 7
      """
    )
    runtime.run()
    assert runtime._root_frame is not None
    cell = runtime._root_frame.vars["ps"]
    self.assertEqual(cell.shape, [2, 2])
    self.assertEqual(cell.value[1]["x"], 5)
    self.assertEqual(cell.value[2]["y"], 7)

  def test_struct_array_procedure_call(self) -> None:
    runtime = self.runtime_for(
      """\
      struct Pair {
          int x,
          int y
      }

      procedure bump(Pair ps[2])
          ps[0].x += 1
          ps[1].y += 2

      procedure main()
          Pair[2] ps
          call bump(ps)
      """
    )
    runtime.run()
    assert runtime._root_frame is not None
    self.assertEqual(
      runtime._root_frame.vars["ps"].value,
      [{"x": 1, "y": 0}, {"x": 0, "y": 2}],
    )

  def test_struct_initializer(self) -> None:
    runtime = self.runtime_for(
      """\
      struct Pair {
          int x,
          int y
      }

      procedure main()
          Pair p = {10, 20}
          skip
      """
    )
    runtime.run()
    assert runtime._root_frame is not None
    self.assertEqual(runtime._root_frame.vars["p"].value, {"x": 10, "y": 20})

  def test_struct_array_initializer(self) -> None:
    runtime = self.runtime_for(
      """\
      struct Pair {
          int x,
          int y
      }

      procedure main()
          Pair ps[3] = {{1, 2}, {3, 4}, {5, 6}}
          skip
      """
    )
    runtime.run()
    assert runtime._root_frame is not None
    self.assertEqual(runtime._root_frame.vars["ps"].value, [{"x": 1, "y": 2}, {"x": 3, "y": 4}, {"x": 5, "y": 6}])

  def test_nested_struct_initializer(self) -> None:
    runtime = self.runtime_for(
      """\
      struct Inner {
          int a,
          int b
      }

      struct Outer {
          int tag,
          Inner inner
      }

      procedure main()
          Outer o = {99, {1, 2}}
          skip
      """
    )
    runtime.run()
    assert runtime._root_frame is not None
    self.assertEqual(runtime._root_frame.vars["o"].value, {"tag": 99, "inner": {"a": 1, "b": 2}})

  def test_partial_struct_initializer(self) -> None:
    runtime = self.runtime_for(
      """\
      struct Pair {
          int x,
          int y
      }

      procedure main()
          Pair p = {42}
          skip
      """
    )
    runtime.run()
    assert runtime._root_frame is not None
    self.assertEqual(runtime._root_frame.vars["p"].value, {"x": 42, "y": 0})

  def test_ternary_expression_selects_branch(self) -> None:
    runtime = self.runtime_for(
      """\
      procedure main()
          int x = 1
          int y = 9
          int z
          z += x = 1 ? y : x
      """
    )
    runtime.run()
    assert runtime._root_frame is not None
    self.assertEqual(runtime._root_frame.vars["z"].value, 9)


if __name__ == "__main__":
  unittest.main()
