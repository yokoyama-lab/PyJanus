"""
Comprehensive grammar coverage tests for the 2026 Janus (PyJanus) parser.

Each test class covers one syntax element.  Tests are organized as:
  - roundtrip: parse → format → compare with source
  - runtime:   parse → run → check stdout
  - error:     parse raises JanaError
"""
from __future__ import annotations

import io
import sys
import textwrap
import unittest
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src"))

from jana_py.errors import JanaError
from jana_py.format import format_program
from jana_py.parser_janus2026 import parse_program
from jana_py.runtime import Runtime


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def roundtrip(source: str) -> str:
    return format_program(parse_program("<test>", source))


def run(source: str) -> str:
    prog = parse_program("<test>", source)
    rt = Runtime(prog)
    rt.run()
    return "".join(rt.stdout)


def run_with_input(source: str, stdin: str) -> str:
    prog = parse_program("<test>", source)
    rt = Runtime(prog)
    with patch("sys.stdin", io.StringIO(stdin)):
        rt.run()
    return "".join(rt.stdout)


# ---------------------------------------------------------------------------
# Procedure definitions
# ---------------------------------------------------------------------------

class ProcedureDefinitionTests(unittest.TestCase):

    def test_empty_main_is_accepted(self) -> None:
        parse_program("<test>", "void main() {}")

    def test_void_style_roundtrip(self) -> None:
        source = textwrap.dedent("""\
            void main() {
                int x;
                call inc(x);
            }

            void inc(int x) {
                x += 1;
            }
            """)
        self.assertEqual(roundtrip(source), source)

    def test_procedure_keyword_is_rejected(self) -> None:
        with self.assertRaises(JanaError):
            parse_program("<test>", textwrap.dedent("""\
                procedure main()
                int x
                call inc(x)

                procedure inc(int x)
                x += 1
                """))

    def test_multiple_params(self) -> None:
        source = textwrap.dedent("""\
            void main() {
                int a;
                int b;
                int c;
                call add3(a, b, c);
            }

            void add3(int a, int b, int c) {
                a += b;
                a += c;
            }
            """)
        self.assertEqual(roundtrip(source), source)

    def test_array_param(self) -> None:
        source = textwrap.dedent("""\
            void main() {
                int arr[4];
                call fill(arr);
            }

            void fill(int arr[4]) {
                arr[0] += 1;
            }
            """)
        self.assertEqual(roundtrip(source), source)

    def test_multiple_main_is_error(self) -> None:
        with self.assertRaises(JanaError):
            parse_program("<test>", textwrap.dedent("""\
                void main() { assert true; }
                void main() { assert true; }
                """))


# ---------------------------------------------------------------------------
# Variable declarations
# ---------------------------------------------------------------------------

class VariableDeclarationTests(unittest.TestCase):

    def test_all_int_types_accepted(self) -> None:
        source = textwrap.dedent("""\
            void main() {
                int a;
                i8 b;
                i16 c;
                i32 d;
                i64 e;
                u8 f;
                u16 g;
                u32 h;
                u64 i;
                bool j;
                a += 1;
            }
            """)
        self.assertEqual(roundtrip(source), source)

    def test_multi_vdecl_same_line(self) -> None:
        prog = parse_program("<test>", textwrap.dedent("""\
            void main() {
                int x1, x2, x3;
                assert (true);
            }
            """))
        self.assertEqual(len(prog.main.vdecls), 3)
        self.assertEqual([v.ident.name for v in prog.main.vdecls], ["x1", "x2", "x3"])

    def test_scalar_init(self) -> None:
        self.assertEqual(run(textwrap.dedent("""\
            void main() {
                int x = 42;
                printf("%d\\n", x);
            }
            """)), "42\n")

    def test_array_init_explicit_size(self) -> None:
        self.assertEqual(run(textwrap.dedent("""\
            void main() {
                int arr[3] = {10, 20, 30};
                printf("%d\\n", arr[1]);
            }
            """)), "20\n")

    def test_array_init_inferred_size(self) -> None:
        self.assertEqual(run(textwrap.dedent("""\
            void main() {
                int arr[] = {1, 2, 3};
                printf("%d\\n", arr[2]);
            }
            """)), "3\n")

    def test_bool_vdecl(self) -> None:
        parse_program("<test>", textwrap.dedent("""\
            void main() {
                bool flag = true;
                assert (true);
            }
            """))

    def test_stack_vdecl(self) -> None:
        run(textwrap.dedent("""\
            void main() {
                int x = 1;
                stack s;
                push(x, s);
                pop(x, s);
            }
            """))


# ---------------------------------------------------------------------------
# Assignment and swap
# ---------------------------------------------------------------------------

class AssignSwapTests(unittest.TestCase):

    def test_add_assign(self) -> None:
        self.assertEqual(run(textwrap.dedent("""\
            void main() {
                int x = 3;
                x += 4;
                printf("%d\\n", x);
            }
            """)), "7\n")

    def test_sub_assign(self) -> None:
        self.assertEqual(run(textwrap.dedent("""\
            void main() {
                int x = 10;
                x -= 3;
                printf("%d\\n", x);
            }
            """)), "7\n")

    def test_xor_assign(self) -> None:
        self.assertEqual(run(textwrap.dedent("""\
            void main() {
                int x = 0b1010;
                x ^= 0b1100;
                printf("%d\\n", x);
            }
            """)), "6\n")

    def test_swap(self) -> None:
        self.assertEqual(run(textwrap.dedent("""\
            void main() {
                int a = 3;
                int b = 7;
                a <=> b;
                printf("%d %d\\n", a, b);
            }
            """)), "7 3\n")

    def test_swap_roundtrip(self) -> None:
        source = textwrap.dedent("""\
            void main() {
                int a;
                int b;
                a <=> b;
            }
            """)
        self.assertEqual(roundtrip(source), source)


# ---------------------------------------------------------------------------
# if statement
# ---------------------------------------------------------------------------

class IfStatementTests(unittest.TestCase):

    def test_if_cstyle_roundtrip(self) -> None:
        source = textwrap.dedent("""\
            void main() {
                int x = 1;
                if (x == 1) {
                    x += 1;
                }
                fi (x == 2);
            }
            """)
        self.assertEqual(roundtrip(source), source)

    def test_if_else_cstyle_roundtrip(self) -> None:
        source = textwrap.dedent("""\
            void main() {
                int x = 0;
                if (x == 0) {
                    x += 1;
                }
                else {
                    x -= 1;
                }
                fi (x == 1);
            }
            """)
        self.assertEqual(roundtrip(source), source)

    def test_if_true_branch_taken(self) -> None:
        self.assertEqual(run(textwrap.dedent("""\
            void main() {
                int x = 5;
                if (x == 5) {
                    x += 1;
                } fi (x == 6);
                printf("%d\\n", x);
            }
            """)), "6\n")

    def test_if_else_branch_taken(self) -> None:
        self.assertEqual(run(textwrap.dedent("""\
            void main() {
                int x = 5;
                if (x == 0) {
                    x += 100;
                } else {
                    x += 1;
                } fi (x == 105);
                printf("%d\\n", x);
            }
            """)), "6\n")

    def test_if_without_fi_is_accepted(self) -> None:
        parse_program("<test>", textwrap.dedent("""\
            void main() {
                int x = 0;
                if (x == 0) {
                    x += 1;
                }
            }
            """))


# ---------------------------------------------------------------------------
# switch statement
# ---------------------------------------------------------------------------

class SwitchStatementTests(unittest.TestCase):

    def test_switch_roundtrip(self) -> None:
        source = textwrap.dedent("""\
            void main() {
                int x = 1;
                switch (x) {
                    case 1:
                        x += 10;
                        break;
                    case 2:
                        x += 20;
                        break;
                } switch (x);
            }
            """)
        self.assertEqual(roundtrip(source), source)

    def test_switch_with_default_roundtrip(self) -> None:
        source = textwrap.dedent("""\
            void main() {
                int x = 99;
                switch (x) {
                    case 1:
                        x += 1;
                        break;
                    default:
                        x += 0;
                        break;
                } switch (x);
            }
            """)
        self.assertEqual(roundtrip(source), source)

    def test_switch_matching_case(self) -> None:
        self.assertEqual(run(textwrap.dedent("""\
            void main() {
                int x = 2;
                switch (x) {
                    case 1:
                        x += 10;
                        break;
                    case 2:
                        x += 20;
                        break;
                } switch (x - 20);
                printf("%d\\n", x);
            }
            """)), "22\n")

    def test_switch_default_taken(self) -> None:
        self.assertEqual(run(textwrap.dedent("""\
            void main() {
                int x = 5;
                switch (x) {
                    case 1:
                        x += 1;
                        break;
                    default:
                        x += 0;
                        break;
                } switch (x);
                printf("%d\\n", x);
            }
            """)), "5\n")

    def test_switch_different_exit_expr(self) -> None:
        source = textwrap.dedent("""\
            void main() {
                int x = 0;
                switch (x) {
                    case 0:
                        x += 1;
                        break;
                } switch (x - 1);
            }
            """)
        parse_program("<test>", source)

    def test_switch_requires_break(self) -> None:
        with self.assertRaises(JanaError):
            parse_program("<test>", textwrap.dedent("""\
                void main() {
                    int x;
                    switch (x) {
                        case 0:
                            assert true;
                    } switch (x);
                }
                """))


# ---------------------------------------------------------------------------
# from loop
# ---------------------------------------------------------------------------

class FromLoopTests(unittest.TestCase):

    def test_from_cstyle_roundtrip(self) -> None:
        source = textwrap.dedent("""\
            void main() {
                int i;
                from (i == 0) {
                    i += 1;
                } loop {
                    i += 1;
                } until (i == 3);
            }
            """)
        self.assertEqual(roundtrip(source), source)

    def test_from_empty_do_roundtrip(self) -> None:
        source = textwrap.dedent("""\
            void main() {
                int i;
                from (i == 0) loop {
                    i += 1;
                } until (i == 3);
            }
            """)
        self.assertEqual(roundtrip(source), source)

    def test_from_runtime(self) -> None:
        # do{+1} then test then loop{+1}: the until-condition is checked at
        # i = 1, 3, 5, ... so it must target a reachable (odd) value.
        self.assertEqual(run(textwrap.dedent("""\
            void main() {
                int i;
                from (i == 0) {
                    i += 1;
                } loop {
                    i += 1;
                } until (i == 5);
                printf("%d\\n", i);
            }
            """)), "5\n")


# ---------------------------------------------------------------------------
# for loop  (C-style)
# ---------------------------------------------------------------------------

class ForLoopTests(unittest.TestCase):

    def test_for_roundtrip(self) -> None:
        source = textwrap.dedent("""\
            void main() {
                int arr[3];
                for (int i = 0; i < 3; i += 1) {
                    arr[i] += i;
                }
            }
            """)
        self.assertEqual(roundtrip(source), source)

    def test_for_runtime(self) -> None:
        self.assertEqual(run(textwrap.dedent("""\
            void main() {
                int sum;
                int arr[4] = {1, 2, 3, 4};
                for (int i = 0; i < 4; i += 1) {
                    sum += arr[i];
                }
                printf("%d\\n", sum);
            }
            """)), "10\n")


# ---------------------------------------------------------------------------
# iterate  (classic style; formats as for loop)
# ---------------------------------------------------------------------------

class IterateTests(unittest.TestCase):

    def test_iterate_parses(self) -> None:
        parse_program("<test>", textwrap.dedent("""\
            void main() {
                int sum;
                iterate int i = 1 to 5
                    sum += i;
                end
            }
            """))

    def test_iterate_formats_as_for(self) -> None:
        # iterate is a legacy syntax; the formatter emits a for loop
        prog = parse_program("<test>", textwrap.dedent("""\
            void main() {
                int sum;
                iterate int i = 0 to 3
                    sum += i;
                end
            }
            """))
        fmt = format_program(prog)
        self.assertIn("for (int i = 0; i < 3; i += 1)", fmt)

    def test_iterate_runtime(self) -> None:
        self.assertEqual(run(textwrap.dedent("""\
            void main() {
                int sum;
                iterate int i = 1 to 5
                    sum += i;
                end
                printf("%d\\n", sum);
            }
            """)), "15\n")


# ---------------------------------------------------------------------------
# local / delocal
# ---------------------------------------------------------------------------

class LocalDelocalTests(unittest.TestCase):

    def test_local_cstyle_roundtrip(self) -> None:
        source = textwrap.dedent("""\
            void main() {
                int x = 3;
                local int tmp = 3 {
                    tmp -= x;
                } delocal int tmp;
            }
            """)
        self.assertEqual(roundtrip(source), source)

    def test_local_runtime(self) -> None:
        self.assertEqual(run(textwrap.dedent("""\
            void main() {
                int x;
                local int tmp = 0 {
                    tmp += 7;
                    x += tmp;
                } delocal int tmp = 7;
                printf("%d\\n", x);
            }
            """)), "7\n")

    def test_multi_local_roundtrip(self) -> None:
        source = textwrap.dedent("""\
            void main() {
                local int a = 1, int b = 2 {
                    a += b;
                } delocal int a = 3, int b = 2;
            }
            """)
        self.assertEqual(roundtrip(source), source)

    def test_local_array_roundtrip(self) -> None:
        source = textwrap.dedent("""\
            void main() {
                local int buf[4] {
                    buf[0] += 1;
                } delocal int buf[4];
            }
            """)
        self.assertEqual(roundtrip(source), source)


# ---------------------------------------------------------------------------
# ancilla / constant
# ---------------------------------------------------------------------------

class AncillaConstantTests(unittest.TestCase):

    def test_ancilla_parses(self) -> None:
        parse_program("<test>", textwrap.dedent("""\
            void main() {
                int x;
                ancilla int tmp = 0;
                x += 1;
            }
            """))

    def test_constant_runtime(self) -> None:
        self.assertEqual(run(textwrap.dedent("""\
            void main() {
                int x;
                constant int k = 10;
                x += k;
                printf("%d\\n", x);
            }
            """)), "10\n")


# ---------------------------------------------------------------------------
# push / pop
# ---------------------------------------------------------------------------

class PushPopTests(unittest.TestCase):

    def test_push_pop_roundtrip(self) -> None:
        source = textwrap.dedent("""\
            void main() {
                int x = 7;
                stack s;
                push(x, s);
                x ^= 7;
                pop(x, s);
            }
            """)
        self.assertEqual(roundtrip(source), source)

    def test_push_pop_runtime(self) -> None:
        self.assertEqual(run(textwrap.dedent("""\
            void main() {
                int x = 42;
                stack s;
                push(x, s);
                pop(x, s);
                printf("%d\\n", x);
            }
            """)), "42\n")


# ---------------------------------------------------------------------------
# call / uncall / bare call
# ---------------------------------------------------------------------------

class CallUncallTests(unittest.TestCase):

    def test_call_uncall_roundtrip(self) -> None:
        source = textwrap.dedent("""\
            void main() {
                int x;
                call inc(x);
                uncall inc(x);
            }

            void inc(int x) {
                x += 1;
            }
            """)
        self.assertEqual(roundtrip(source), source)

    def test_bare_call_normalizes_to_call(self) -> None:
        prog = parse_program("<test>", textwrap.dedent("""\
            void main() {
                int x;
                inc(x);
            }

            void inc(int x) {
                x += 1;
            }
            """))
        self.assertIn("call inc(x);", format_program(prog))

    def test_call_external_roundtrip(self) -> None:
        source = textwrap.dedent("""\
            void main() {
                int x;
                call external inc(x);
                uncall external inc(x);
            }
            """)
        self.assertEqual(roundtrip(source), source)


# ---------------------------------------------------------------------------
# I/O: printf, scanf, assert
# ---------------------------------------------------------------------------

class IoStatementTests(unittest.TestCase):

    def test_printf_roundtrip(self) -> None:
        source = textwrap.dedent("""\
            void main() {
                int x = 99;
                printf("%d\\n", x);
            }
            """)
        self.assertEqual(roundtrip(source), source)

    def test_scanf_roundtrip(self) -> None:
        source = textwrap.dedent("""\
            void main() {
                int x;
                scanf("%d", x);
            }
            """)
        self.assertEqual(roundtrip(source), source)

    def test_scanf_runtime(self) -> None:
        self.assertEqual(
            run_with_input(textwrap.dedent("""\
                void main() {
                    int x;
                    scanf("%d", x);
                    printf("%d\\n", x);
                }
                """), "42\n"),
            "42\n",
        )

    def test_skip_keyword_is_rejected(self) -> None:
        with self.assertRaises(JanaError):
            parse_program("<test>", textwrap.dedent("""\
                void main() {
                    skip;
                }
                """))

    def test_assert_passes(self) -> None:
        run(textwrap.dedent("""\
            void main() {
                int x = 5;
                assert (x == 5);
            }
            """))

    def test_assert_fails_raises(self) -> None:
        with self.assertRaises(JanaError):
            run(textwrap.dedent("""\
                void main() {
                    int x = 5;
                    assert (x == 0);
                }
                """))

    def test_assert_roundtrip(self) -> None:
        # The parser requires the condition to be parenthesized, while the
        # formatter prints it without parentheses, so this is a parse->format
        # check rather than an exact round-trip.
        source = textwrap.dedent("""\
            void main() {
                int x = 5;
                assert (x == 5);
            }
            """)
        self.assertEqual(roundtrip(source), source.replace("assert (x == 5)", "assert x == 5"))


# ---------------------------------------------------------------------------
# Expressions
# ---------------------------------------------------------------------------

class ExpressionTests(unittest.TestCase):

    def test_arithmetic_precedence(self) -> None:
        # 2 + 4*5 - 1 = 21, x starts 3 → 3 + 21 = 24
        self.assertEqual(run(textwrap.dedent("""\
            void main() {
                int x = 3;
                x += 2 + 4 * 5 - 1;
                printf("%d\\n", x);
            }
            """)), "24\n")

    def test_bitwise_and(self) -> None:
        self.assertEqual(run(textwrap.dedent("""\
            void main() {
                int x;
                x += 0b1010 & 0b1100;
                printf("%d\\n", x);
            }
            """)), "8\n")

    def test_bitwise_or(self) -> None:
        self.assertEqual(run(textwrap.dedent("""\
            void main() {
                int x;
                x += 0b1010 | 0b1100;
                printf("%d\\n", x);
            }
            """)), "14\n")

    def test_shift_left(self) -> None:
        self.assertEqual(run(textwrap.dedent("""\
            void main() {
                int x;
                x += 1 << 4;
                printf("%d\\n", x);
            }
            """)), "16\n")

    def test_shift_right(self) -> None:
        self.assertEqual(run(textwrap.dedent("""\
            void main() {
                int x;
                x += 32 >> 2;
                printf("%d\\n", x);
            }
            """)), "8\n")

    def test_prefix_logical_not(self) -> None:
        self.assertEqual(run(textwrap.dedent("""\
            void main() {
                int x;
                x += (!false ? 1 : 0);
                printf("%d\\n", x);
            }
            """)), "1\n")

    def test_prefix_negate(self) -> None:
        self.assertEqual(run(textwrap.dedent("""\
            void main() {
                int x = 5;
                x += -3;
                printf("%d\\n", x);
            }
            """)), "2\n")

    def test_ternary_with_parens(self) -> None:
        self.assertEqual(run(textwrap.dedent("""\
            void main() {
                int x;
                x += (1 == 1 ? 10 : 20);
                printf("%d\\n", x);
            }
            """)), "10\n")

    def test_ternary_bare_in_update_is_error(self) -> None:
        with self.assertRaises(JanaError):
            parse_program("<test>", textwrap.dedent("""\
                void main() {
                    int x;
                    int y;
                    x += y == 0 ? 1 : 2;
                }
                """))

    def test_type_cast(self) -> None:
        # (u8)300 wraps to 44
        self.assertEqual(run(textwrap.dedent("""\
            void main() {
                int big = 300;
                local u8 b = (u8)big {
                    printf("%d\\n", b);
                } delocal u8 b = (u8)big;
            }
            """)), "44\n")

    def test_binary_literal(self) -> None:
        self.assertEqual(run(textwrap.dedent("""\
            void main() {
                int x = 0b1111;
                printf("%d\\n", x);
            }
            """)), "15\n")

    def test_empty_and_size(self) -> None:
        self.assertEqual(run(textwrap.dedent("""\
            void main() {
                stack s;
                int x = 5;
                local int was_empty = (empty(s) ? 1 : 0) {
                    printf("%d\\n", was_empty);
                    push(x, s);
                    local int sz = size(s) {
                        printf("%d\\n", sz);
                    } delocal int sz = 1;
                    pop(x, s);
                } delocal int was_empty = 1;
            }
            """)), "1\n1\n")

    def test_logical_and_or(self) -> None:
        self.assertEqual(run(textwrap.dedent("""\
            void main() {
                int x;
                x += (1 == 1 && 2 == 2 ? 1 : 0);
                x += (1 == 0 || 2 == 2 ? 2 : 0);
                printf("%d\\n", x);
            }
            """)), "3\n")

    def test_lval_array_index(self) -> None:
        self.assertEqual(run(textwrap.dedent("""\
            void main() {
                int arr[3] = {10, 20, 30};
                arr[1] += 5;
                printf("%d\\n", arr[1]);
            }
            """)), "25\n")


# ---------------------------------------------------------------------------
# Struct
# ---------------------------------------------------------------------------

class StructTests(unittest.TestCase):

    def test_struct_def_roundtrip(self) -> None:
        source = textwrap.dedent("""\
            struct Pair {
                int left;
                int right;
            };

            void main() {
                Pair p;
                p.left += 1;
                p.right += 2;
            }
            """)
        self.assertEqual(roundtrip(source), source)

    def test_struct_trailing_semicolon_accepted(self) -> None:
        parse_program("<test>", textwrap.dedent("""\
            struct Foo {
                int x;
            };

            void main() {
                assert (true);
            }
            """))

    def test_struct_field_access_runtime(self) -> None:
        self.assertEqual(run(textwrap.dedent("""\
            struct Point {
                int x;
                int y;
            };

            void main() {
                Point p;
                p.x += 3;
                p.y += 7;
                printf("%d %d\\n", p.x, p.y);
            }
            """)), "3 7\n")

    def test_struct_array_field(self) -> None:
        self.assertEqual(run(textwrap.dedent("""\
            struct Vec {
                int v[3];
            };

            void main() {
                Vec u;
                u.v[1] += 42;
                printf("%d\\n", u.v[1]);
            }
            """)), "42\n")


# ---------------------------------------------------------------------------
# Error cases
# ---------------------------------------------------------------------------

class ParseErrorTests(unittest.TestCase):

    def test_unexpected_token(self) -> None:
        with self.assertRaises(JanaError):
            parse_program("<test>", "???")

    def test_unclosed_brace(self) -> None:
        with self.assertRaises(JanaError):
            parse_program("<test>", textwrap.dedent("""\
                void main() {
                    int x;
                """))

    def test_missing_proc_keyword(self) -> None:
        with self.assertRaises(JanaError):
            parse_program("<test>", textwrap.dedent("""\
                int main() {
                    assert true;
                }
                """))


if __name__ == "__main__":
    unittest.main()
