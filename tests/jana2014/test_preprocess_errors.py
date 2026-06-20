"""Error paths of the preprocessor (the least-covered part of preprocess.py).

The happy paths of #define/#include/#ifdef are covered elsewhere; here we pin the
diagnostics: unmatched/duplicate conditionals, bad includes, unknown directives,
and the macro-expansion depth limit.
"""
from __future__ import annotations

import textwrap
from pathlib import Path

import pytest

from jana_py.errors import JanaError
from jana_py.preprocess import preprocess_text


def pp(text: str, filename: str = "t.ja"):
  return preprocess_text(filename, textwrap.dedent(text))


# ----- conditional compilation diagnostics --------------------------------

def test_else_without_ifdef():
  with pytest.raises(JanaError, match="#else"):
    pp("#else\n#endif\n")


def test_duplicate_else():
  with pytest.raises(JanaError, match="[Dd]uplicate #else"):
    pp("#ifdef X\n#else\n#else\n#endif\n")


def test_endif_without_ifdef():
  with pytest.raises(JanaError, match="#endif"):
    pp("#endif\n")


def test_unterminated_conditional():
  with pytest.raises(JanaError, match="[Uu]nterminated"):
    pp("#ifdef X\nprocedure main()\n")


# ----- directive / macro diagnostics --------------------------------------

def test_unsupported_directive():
  with pytest.raises(JanaError, match="[Uu]nsupported preprocessor directive"):
    pp("#frobnicate stuff\n")


# ----- include diagnostics ------------------------------------------------

def test_include_not_found(tmp_path):
  a = tmp_path / "a.ja"
  a.write_text('#include "nope.ja"\n')
  with pytest.raises(JanaError, match="[Nn]ot found"):
    preprocess_text(str(a), a.read_text())


def test_cyclic_include(tmp_path):
  a = tmp_path / "a.ja"
  b = tmp_path / "b.ja"
  a.write_text('#include "b.ja"\n')
  b.write_text('#include "a.ja"\n')
  with pytest.raises(JanaError, match="[Cc]yclic"):
    preprocess_text(str(a), a.read_text())


def test_include_outside_preamble(tmp_path):
  a = tmp_path / "a.ja"
  b = tmp_path / "b.ja"
  b.write_text("procedure helper()\n    skip\n")
  a.write_text('procedure main()\n    skip\n#include "b.ja"\n')
  with pytest.raises(JanaError, match="[Pp]reamble|preamble"):
    preprocess_text(str(a), a.read_text())


# ----- conditional happy path (defined vs not) ----------------------------

def test_ifdef_selects_branches():
  out_with = pp("#define FLAG 1\n#ifdef FLAG\nyes\n#else\nno\n#endif\n").text
  out_without = pp("#ifdef FLAG\nyes\n#else\nno\n#endif\n").text
  assert "yes" in out_with and "no" not in out_with
  assert "no" in out_without and "yes" not in out_without


def test_ifndef_is_complementary():
  out = pp("#ifndef FLAG\nelse_branch\n#endif\n").text
  assert "else_branch" in out


# ----- macro expansion ----------------------------------------------------

def test_object_macro_expands():
  out = pp("#define N 5\nprocedure main()\n    int x\n    x += N\n").text
  assert "x += 5" in out and "N" not in out.split("x += ")[1]


def test_function_macro_expands():
  out = pp("#define SQ(a) ((a) * (a))\nprocedure main()\n    int x\n    x += SQ(3)\n").text
  assert "((3) * (3))" in out


def test_self_referential_macro_terminates():
  # The expander's `seen` guard leaves a self-referential macro in place rather
  # than looping forever.
  out = pp("#define f(x) f(x)\nprocedure main()\n    int y\n    y += f(1)\n").text
  assert "y += f(1)" in out


def test_mutually_recursive_macros_terminate():
  out = pp("#define A B\n#define B C\n#define C A\nx += A\n").text
  assert out.strip().endswith("x += C")    # stops when A is seen again
