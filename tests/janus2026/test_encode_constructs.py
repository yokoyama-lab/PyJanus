"""Encoder coverage for every Janus-0 construct the self-interpreter accepts.

`jana_py.encode` flattens a Janus-0 AST into the integer `code[]`/proc-table
arrays the self-interpreter (`modern_interpreter.ja`) consumes.  The existing
`test_self_interp.py` only checks the three scalar update opcodes; this file
drives every remaining construct (control flow, arrays, calls, local/delocal)
and the error paths, plus the `generate_janus` source emitter.

Each encoded statement block is framed as `[TAG, TOTAL_LEN, ...payload...,
TOTAL_LEN]`, so the framing invariant (first and last word of a block agree and
equal its length) is a strong, construct-agnostic correctness check that we
assert alongside the leading opcode.
"""
from __future__ import annotations

import pytest

from jana_py.ast import SkipStmt, SourcePos
from jana_py.encode import (
    Encoder, encode_program, generate_janus,
    S_ADDEQ, S_SUBEQ, S_SWAP, S_IF, S_FROM, S_CALL, S_UNCALL, S_SKIP,
    E_CONST, E_VAR, E_ARRIDX, E_BINOP, L_VAR, L_ARRIDX,
)


def _framed(block: list[int]) -> bool:
  """A well-formed encoded block: len field at index 1 frames the whole block."""
  return len(block) >= 4 and block[1] == len(block) and block[-1] == len(block)


class TestControlFlow:

  def test_skip_opcode(self):
    # `skip` is not surface syntax in the janus2026 dialect, so exercise the
    # encoder's SkipStmt path directly.
    block = Encoder().encode_stmt(SkipStmt(SourcePos("t", 0, 0)))
    assert block[0] == S_SKIP
    assert _framed(block), block

  def test_if_fi_framing_and_branches(self):
    src = (
      "void main() {\n"
      "    int x;\n"
      "    int y;\n"
      "    if (x == 0) { y += 1; } else { y += 2; } fi (y == 1);\n"
      "}\n"
    )
    r = encode_program(src)
    assert r.code[0] == S_IF
    assert _framed(r.code), r.code
    # both branch bodies are S_ADDEQ updates somewhere inside the block
    assert S_ADDEQ in r.code

  def test_from_until_loop(self):
    src = (
      "void main() {\n"
      "    int i;\n"
      "    from (i == 0) { i += 1; } loop { i += 1; } until (i == 4);\n"
      "}\n"
    )
    r = encode_program(src)
    assert r.code[0] == S_FROM
    assert _framed(r.code), r.code


class TestArrays:

  def test_array_decl_allocates_slots(self):
    r = encode_program("void main() {\n    int a[3];\n    a[0] += 5;\n}\n")
    assert r.var_map["a"].size == 3
    assert r.store_size >= 3

  def test_array_index_as_lvalue_target(self):
    # a[1] += 7  ->  S_ADDEQ with an L_ARRIDX target
    r = encode_program("void main() {\n    int a[3];\n    a[1] += 7;\n}\n")
    assert r.code[0] == S_ADDEQ
    assert L_ARRIDX in r.code

  def test_array_index_as_rvalue(self):
    # x += a[0]  ->  the RHS expression is an E_ARRIDX read
    r = encode_program("void main() {\n    int x;\n    int a[3];\n    x += a[0];\n}\n")
    assert r.code[0] == S_ADDEQ
    assert E_ARRIDX in r.code

  def test_nonconstant_array_size_rejected(self):
    # Array dimensions must be literal constants for the flat store layout.
    src = "void main() {\n    int n;\n    int a[n];\n}\n"
    with pytest.raises(ValueError, match="[Aa]rray size"):
      encode_program(src)


class TestCalls:

  def _prog(self, body_main: str) -> str:
    return (
      "void inc(int a) {\n    a += 1;\n}\n"
      "void main() {\n    int x;\n" + body_main + "}\n"
    )

  def test_call_opcode_and_proc_table(self):
    # code[] holds procedure bodies first, then main; the call/uncall sits at
    # main_code_offset.
    r = encode_program(self._prog("    call inc(x);\n"))
    assert r.code[r.main_code_offset] == S_CALL
    assert any(p.name == "inc" for p in r.procs)

  def test_uncall_opcode(self):
    r = encode_program(self._prog("    uncall inc(x);\n"))
    assert r.code[r.main_code_offset] == S_UNCALL

  def test_unknown_procedure_rejected(self):
    src = "void main() {\n    int x;\n    call nope(x);\n}\n"
    with pytest.raises(ValueError, match="[Uu]nknown procedure"):
      encode_program(src)


class TestLocalDelocal:

  def test_local_delocal_expands_to_add_then_sub(self):
    # local int t = 0; t += a; delocal int t = a  expands to an S_ADDEQ ... S_SUBEQ
    # bracket around the body.
    src = (
      "void main() {\n"
      "    int a;\n"
      "    a += 4;\n"
      "    local int t = 0 {\n"
      "        t += a;\n"
      "    } delocal int t = a;\n"
      "}\n"
    )
    r = encode_program(src)
    assert S_ADDEQ in r.code and S_SUBEQ in r.code
    # the local var got its own slot
    assert "t" in r.var_map


class TestSwapAndExpr:

  def test_swap_opcode(self):
    r = encode_program("void main() {\n    int x;\n    int y;\n    x <=> y;\n}\n")
    assert r.code[0] == S_SWAP
    assert _framed(r.code), r.code

  def test_binop_expression_encoding(self):
    r = encode_program("void main() {\n    int x;\n    int y;\n    x += y + 2;\n}\n")
    assert E_BINOP in r.code
    assert E_VAR in r.code and E_CONST in r.code


class TestGenerateJanus:
  """generate_janus emits a runnable Janus wrapper around the encoded arrays."""

  def test_emits_vm_setup_and_store_prints(self):
    r = encode_program("void main() {\n    int x;\n    x += 5;\n}\n")
    out = generate_janus(r)
    assert "void main()" in out
    assert "vm.code +=" in out
    assert "call exec_stmts(vm);" in out
    assert "uncall exec_stmts(vm);" in out
    # scalar x is printed from its store slot
    assert "x = %d" in out
    assert f"vm.store[{r.var_map['x'].slot}]" in out

  def test_custom_interp_path_is_included(self):
    r = encode_program("void main() {\n    int x;\n    x += 1;\n}\n")
    out = generate_janus(r, interp_path="my_interp.ja")
    assert '#include "my_interp.ja"' in out

  def test_proc_table_emitted_when_procs_present(self):
    src = "void inc(int a) {\n    a += 1;\n}\nvoid main() {\n    int x;\n    call inc(x);\n}\n"
    out = generate_janus(encode_program(src))
    assert "vm.procs +=" in out

  def test_array_var_printed_as_comment_not_scalar(self):
    out = generate_janus(encode_program("void main() {\n    int a[3];\n    a[0] += 1;\n}\n"))
    # arrays are not scalar-printed; they appear as a slot-range comment
    assert "// a[3]" in out
