from __future__ import annotations

from pathlib import Path
import sys
import textwrap
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src"))

from jana_py.errors import JanaError
from jana_py.format import format_program
from jana_py.parser_janus2026 import parse_program
from jana_py.runtime import Runtime


class CStyleSyntaxTests(unittest.TestCase):
  def test_formatter_emits_c_style_for_for_and_switch_break(self) -> None:
    source = textwrap.dedent(
      """\
      void main() {
          int arr[3];
          call visit(arr);
      }

      void visit(int arr[3]) {
          for (int i = 0; i < 3; i += 1) {
              arr[i] += i;
          }
          for (int i = 0; i < 3; i += 1) {
              switch (arr[i]) {
                  case 0:
                      arr[i] += 1;
                      break;
                  default:
                      arr[i] += 1;
                      break;
              } switch (arr[i]);
          }
      }
      """
    )
    program = parse_program("cstyle_roundtrip.ja", source)
    self.assertEqual(format_program(program), source)

  def test_switch_requires_break(self) -> None:
    source = textwrap.dedent(
      """\
      void main() {
          int x;
          switch (x) {
              case 0:
                  assert true;
          } switch (x);
      }
      """
    )
    with self.assertRaises(JanaError):
      parse_program("switch_break_required.ja", source)

  def test_update_ternary_requires_parentheses(self) -> None:
    source = textwrap.dedent(
      """\
      void main() {
          int x;
          int y;
          x += y == 0 ? 1 : 2;
      }
      """
    )
    with self.assertRaises(JanaError):
      parse_program("ternary_needs_parens.ja", source)

  def test_parenthesized_update_ternary_is_allowed(self) -> None:
    source = textwrap.dedent(
      """\
      void main() {
          int x;
          int y;
          x += (y == 0 ? 1 : 2);
      }
      """
    )
    parse_program("ternary_with_parens.ja", source)

  def test_multi_local_shorthand_round_trips(self) -> None:
    source = textwrap.dedent(
      """\
      void main() {
          local int x = 3, int y = 7, int z {
              call elegant_pair(x, y, z);
              printf("%d", z);
              uncall elegant_pair(x, y, z);
          } delocal int x = 3, int y = 7, int z;
      }

      void elegant_pair(int x, int y, int z) {
          z += x;
          z += y;
      }
      """
    )
    program = parse_program("multi_local_shorthand.ja", source)
    self.assertEqual(format_program(program), source)

  def test_nested_multi_local_formats_to_shorthand(self) -> None:
    source = textwrap.dedent(
      """\
      void main() {
          local int x = 3 {
              local int y = 7 {
                  local int z = 0 {
                      call elegant_pair(x, y, z);
                      printf("%d", z);
                      uncall elegant_pair(x, y, z);
                  } delocal int z = 0;
              } delocal int y = 7;
          } delocal int x = 3;
      }

      void elegant_pair(int x, int y, int z) {
          z += x;
          z += y;
      }
      """
    )
    canonical = textwrap.dedent(
      """\
      void main() {
          local int x = 3, int y = 7, int z {
              call elegant_pair(x, y, z);
              printf("%d", z);
              uncall elegant_pair(x, y, z);
          } delocal int x = 3, int y = 7, int z;
      }

      void elegant_pair(int x, int y, int z) {
          z += x;
          z += y;
      }
      """
    )
    program = parse_program("nested_multi_local.ja", source)
    self.assertEqual(format_program(program), canonical)

  def test_multi_vdecls_in_main_and_params_are_accepted(self) -> None:
    source = textwrap.dedent(
      """\
      void main() {
          int x1, x2;
          call pair(x1, x2);
      }

      void pair(int x, int y) {
          x += 1;
          y += 1;
      }
      """
    )
    program = parse_program("multi_vdecls.ja", source)
    self.assertEqual(len(program.main.vdecls), 2)
    self.assertEqual([v.ident.name for v in program.main.vdecls], ["x1", "x2"])
    self.assertEqual([v.ident.name for v in program.procs[0].params], ["x", "y"])

  def test_formatter_omits_zero_init_for_local_and_delocal(self) -> None:
    source = textwrap.dedent(
      """\
      void main() {
          local int shown_count = 0, int shown_head = 0 {
              assert (true);
          } delocal int shown_count = 0, int shown_head = 0;
      }
      """
    )
    canonical = textwrap.dedent(
      """\
      void main() {
          local int shown_count, int shown_head {
              assert true;
          } delocal int shown_count, int shown_head;
      }
      """
    )
    program = parse_program("local_zero_omission.ja", source)
    self.assertEqual(format_program(program), canonical)

  def test_empty_cstyle_from_do_block_can_be_omitted(self) -> None:
    source = textwrap.dedent(
      """\
      void main() {
          int i;
          int j;
          from (i == j + 1) loop {
              i += 1;
          } until (i == j + 2);
      }
      """
    )
    program = parse_program("from_empty_do_omitted.ja", source)
    self.assertEqual(format_program(program), source)

  def test_bare_call_statement_is_accepted(self) -> None:
    source = textwrap.dedent(
      """\
      void main() {
          int x;
          int y;
          mult(x, y);
      }

      void mult(int x, int y) {
          x += y;
          x -= y;
      }
      """
    )
    canonical = textwrap.dedent(
      """\
      void main() {
          int x;
          int y;
          call mult(x, y);
      }

      void mult(int x, int y) {
          x += y;
          x -= y;
      }
      """
    )
    program = parse_program("bare_call.ja", source)
    self.assertEqual(format_program(program), canonical)

  def test_delocal_array_can_omit_explicit_size(self) -> None:
    source = textwrap.dedent(
      """\
      void main() {
          local int dec[8] = {0} {
              assert (true);
          } delocal int dec[] = {0};
      }
      """
    )
    program = parse_program("delocal_array_size_inferred.ja", source)
    Runtime(program).run()

  def test_local_array_zero_shorthands_are_accepted(self) -> None:
    source = textwrap.dedent(
      """\
      void main() {
          local int enc[8] = {0} {
              assert (true);
          } delocal int enc[8] = {0};

          local int dec[8] {
              assert (true);
          } delocal int dec[8];
      }
      """
    )
    program = parse_program("local_array_zero_shorthands.ja", source)
    Runtime(program).run()


if __name__ == "__main__":
  unittest.main()
