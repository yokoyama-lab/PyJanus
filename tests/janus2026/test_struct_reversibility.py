"""Struct reversibility (call+uncall = identity) for the janus2026 dialect.

Structs are a janus2026-only feature, so these cases live here rather than in
the jana2014 reversibility suite.
"""
from __future__ import annotations

from pathlib import Path
import sys
import textwrap
import unittest
import copy

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from jana_py.parser_janus2026 import parse_program
from jana_py.runtime import Runtime
from jana_py.validate import validate_program


def run_and_get_store(source: str) -> dict[str, object]:
  program = parse_program("struct_rev.ja", textwrap.dedent(source))
  validate_program(program)
  rt = Runtime(program)
  rt.run()
  assert rt._root_frame is not None
  return {k: copy.deepcopy(c.value) for k, c in rt._root_frame.vars.items()}


class StructReversibilityTests(unittest.TestCase):
  def assertRoundTrip(self, proc_source: str, main_vars: str, call_args: str) -> None:
    rt_source = f"""\
      {proc_source}

      void main() {{
          {main_vars}
          call {call_args};
          uncall {call_args};
      }}
      """
    init_source = f"""\
      {proc_source}

      void main() {{
          {main_vars}
      }}
      """
    self.assertEqual(
      run_and_get_store(rt_source),
      run_and_get_store(init_source),
      "call+uncall did not restore initial state",
    )

  def test_struct_fields(self) -> None:
    self.assertRoundTrip(
      "struct Pair {\n          int x,\n          int y\n      }\n\n"
      "      void bump(Pair p) {\n          p.x += 1;\n          p.y += 2;\n      }",
      "Pair p;",
      "bump(p)",
    )

  def test_struct_array(self) -> None:
    self.assertRoundTrip(
      "struct Pair {\n          int x,\n          int y\n      }\n\n"
      "      void fill(Pair ps[3]) {\n          ps[0].x += 10;\n          ps[1].y += 20;\n          ps[2].x += 30;\n      }",
      "Pair ps[3];",
      "fill(ps)",
    )


if __name__ == "__main__":
  unittest.main()
