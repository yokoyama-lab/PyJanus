from __future__ import annotations

import os
from pathlib import Path
import subprocess
import sys
import tempfile
import textwrap
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from jana_py.format import format_program
from jana_py.parser import parse_program


def run_python(args: list[str]) -> subprocess.CompletedProcess[str]:
  env = dict(os.environ)
  env["PYTHONPATH"] = str(ROOT)
  return subprocess.run(
    [sys.executable, "-m", "jana_py.cli", *args],
    cwd=ROOT,
    text=True,
    capture_output=True,
    env=env,
    check=False,
  )


class StructParseTests(unittest.TestCase):
  def test_format_round_trip_for_struct_program(self) -> None:
    source = textwrap.dedent(
      """\
      struct Pair {
          int x,
          int y
      }

      procedure main()
          Pair p
          call bump(p)

      procedure bump(Pair p)
          skip
      """
    )
    program = parse_program("struct_roundtrip.ja", source)
    self.assertEqual(format_program(program), source)

  def test_parse_struct_definition_and_main_variable(self) -> None:
    program = parse_program(
      "struct_parse.ja",
      textwrap.dedent(
        """\
        struct Pair {
            int x,
            int y
        }

        procedure main()
            Pair p
            skip
        """
      ),
    )
    self.assertEqual(len(program.struct_defs), 1)
    struct_def = program.struct_defs[0]
    self.assertEqual(struct_def.ident.name, "Pair")
    self.assertEqual([field.ident.name for field in struct_def.fields], ["x", "y"])
    self.assertIsNotNone(program.main)
    self.assertEqual(program.main.vdecls[0].typ.kind, "struct")
    self.assertEqual(program.main.vdecls[0].typ.name, "Pair")

  def test_parse_struct_type_in_procedure_arguments(self) -> None:
    program = parse_program(
      "struct_proc_arg.ja",
      textwrap.dedent(
        """\
        struct Pair {
            int x,
            int y
        }

        procedure bump(Pair p)
            skip

        procedure main()
            Pair p
            call bump(p)
        """
      ),
    )
    self.assertEqual(program.procs[0].params[0].typ.kind, "struct")
    self.assertEqual(program.procs[0].params[0].typ.name, "Pair")

  def test_parse_struct_field_array_dimensions(self) -> None:
    program = parse_program(
      "struct_field_array.ja",
      textwrap.dedent(
        """\
        struct Entry {
            int k
        }

        struct Dict {
            int size,
            Entry entries[4]
        }

        procedure main()
            Dict d
            skip
        """
      ),
    )
    dict_def = program.struct_defs[1]
    self.assertEqual(dict_def.fields[1].ident.name, "entries")
    self.assertEqual(len(dict_def.fields[1].dimensions), 1)

  def test_cli_ast_contains_struct_definitions(self) -> None:
    with tempfile.NamedTemporaryFile("w", suffix=".ja", dir=ROOT, delete=False) as handle:
      handle.write(textwrap.dedent(
        """\
        struct Pair {
            int x,
            int y
        }

        procedure main()
            Pair p
            skip
        """
      ))
      path = handle.name
    try:
      result = run_python(["-a", path])
    finally:
      Path(path).unlink(missing_ok=True)
    self.assertEqual(result.returncode, 0)
    self.assertIn('"struct_defs"', result.stdout)
    self.assertIn('"name": "Pair"', result.stdout)
    self.assertIn('"kind": "struct"', result.stdout)


  def test_parse_struct_array_dims_before_name(self) -> None:
    program = parse_program(
      "struct_array.ja",
      textwrap.dedent(
        """\
        struct Pair {
            int x,
            int y
        }

        procedure main()
            Pair[3] ps
            skip
        """
      ),
    )
    vdecl = program.main.vdecls[0]
    self.assertEqual(vdecl.ident.name, "ps")
    self.assertEqual(vdecl.typ.kind, "struct")
    self.assertEqual(vdecl.typ.name, "Pair")
    self.assertEqual(len(vdecl.dimensions), 1)

  def test_parse_struct_2d_array_dims_before_name(self) -> None:
    program = parse_program(
      "struct_2d.ja",
      textwrap.dedent(
        """\
        struct Pair {
            int x,
            int y
        }

        procedure main()
            Pair[2][2] ps
            skip
        """
      ),
    )
    vdecl = program.main.vdecls[0]
    self.assertEqual(vdecl.ident.name, "ps")
    self.assertEqual(len(vdecl.dimensions), 2)

  def test_format_round_trip_struct_array(self) -> None:
    source = textwrap.dedent(
      """\
      struct Pair {
          int x,
          int y
      }

      procedure main()
          Pair ps[3]
          skip
      """
    )
    program = parse_program("struct_arr_rt.ja", source)
    self.assertEqual(format_program(program), source)


if __name__ == "__main__":
  unittest.main()
