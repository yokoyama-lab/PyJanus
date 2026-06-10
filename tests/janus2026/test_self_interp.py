"""Tests for the Janus self-interpreter encoder.

Only the encoder unit tests are kept here; the end-to-end self-interpreter
execution tests required example assets that are not part of this repo.
"""

from __future__ import annotations

from jana_py.encode import encode_program
from jana_py.encode import (
    S_ADDEQ, S_SUBEQ, S_XOREQ, S_SWAP,
    E_BINOP,
)


class TestEncoderBasic:

    def test_encode_addeq_const(self):
        src = "void main() {\n    int x;\n    x += 5;\n}\n"
        result = encode_program(src)
        assert result.code[0] == S_ADDEQ

    def test_encode_subeq(self):
        src = "void main() {\n    int x;\n    x -= 3;\n}\n"
        result = encode_program(src)
        assert result.code[0] == S_SUBEQ

    def test_encode_xoreq(self):
        src = "void main() {\n    int x;\n    x ^= 7;\n}\n"
        result = encode_program(src)
        assert result.code[0] == S_XOREQ

    def test_encode_muleq_raises_clean_error(self):
        # *=//= have no opcodes.ja tags; encoding must fail with a clear
        # message, not a bare KeyError.
        import pytest
        src = "void main() {\n    int x;\n    x *= 3;\n}\n"
        with pytest.raises(ValueError, match=r"Unsupported assignment operator.*\*="):
            encode_program(src)

    def test_encode_diveq_raises_clean_error(self):
        import pytest
        src = "void main() {\n    int x;\n    x /= 3;\n}\n"
        with pytest.raises(ValueError, match="Unsupported assignment operator"):
            encode_program(src)

    def test_encode_value_arg_raises_clean_error(self):
        # Value (expression) arguments are outside the Janus-0 subset; encoding
        # must fail with a clear message, not a bare type error.
        import pytest
        src = (
            "void f(int n, int r) {\n    r += n;\n}\n"
            "void main() {\n    int n;\n    int r;\n    n += 5;\n    call f(n - 1, r);\n}\n"
        )
        with pytest.raises(ValueError, match="not supported by self-interpreter encoding"):
            encode_program(src)

    def test_encode_swap(self):
        src = "void main() {\n    int x;\n    int y;\n    x <=> y;\n}\n"
        result = encode_program(src)
        assert result.code[0] == S_SWAP

    def test_encode_binexpr(self):
        src = "void main() {\n    int x;\n    int a;\n    int b;\n    x += a + b;\n}\n"
        result = encode_program(src)
        assert E_BINOP in result.code

    def test_var_slots(self):
        src = "void main() {\n    int x;\n    int y;\n    int z;\n    x += 1;\n}\n"
        result = encode_program(src)
        assert result.var_map["x"].slot == 0
        assert result.var_map["y"].slot == 1
        assert result.var_map["z"].slot == 2

    def test_array_slots(self):
        src = "void main() {\n    int a[5];\n    int x;\n    x += 1;\n}\n"
        result = encode_program(src)
        assert result.var_map["a"].slot == 0
        assert result.var_map["a"].size == 5
        assert result.var_map["x"].slot == 5

    def test_procedure_encoding(self):
        src = "void inc(int x) {\n    x += 1;\n}\nvoid main() {\n    int x;\n    call inc(x);\n}\n"
        result = encode_program(src)
        assert len(result.procs) == 1
        assert result.procs[0].name == "inc"
