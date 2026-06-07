"""Tests for the --std janus1982 (strict) and janus1982ext (extended) parsers.

These tests use the original 1982 Janus syntax (Lutz & Derby):
  - Global variable declarations (no type keywords)
  - procedure name  (no parentheses, no parameters)
  - call / uncall   (no parentheses)
  - a : b           (swap with colon)
  - a != expr       (XOR update)
  - #               (not-equal comparison)
  - \\               (integer remainder)
  - ;               (line comment)

Tests using extended features (parameterized procedures) use --std=janus1982ext.
"""
from __future__ import annotations
import sys
import textwrap
import pytest
from jana_py.cli import main


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _run(tmp_path, source, stdin_text=None, extra_args=()):
    path = tmp_path / "prog.ja"
    path.write_text(textwrap.dedent(source))
    argv = ["--std", "janus1982"] + list(extra_args) + [str(path)]
    if stdin_text is not None:
        import io
        import monkeypatch  # will be injected via fixture — see callers
    return argv, path


# ---------------------------------------------------------------------------
# Existing regression tests (hybrid syntax, kept for compatibility)
# ---------------------------------------------------------------------------

def test_janus1982_hybrid_fib(capsys, tmp_path):
    """Procedures with parameters still parse under janus1982ext mode."""
    source = """
    procedure fib(n, x1, x2)
        if n = 0 then
            x1 += 1
            x2 += 1
        else
            n -= 1
            call fib(n, x1, x2)
            x1 += x2
            x1 <=> x2
        fi x1 = x2

    procedure main()
        n += 4
        call fib(n, x1, x2)
    """
    path = tmp_path / "fib82.ja"
    path.write_text(textwrap.dedent(source))
    main(["--std", "janus1982ext", "-s", str(path)])
    out, _ = capsys.readouterr()
    assert "n = 0" in out
    assert "x1 = 5" in out
    assert "x2 = 8" in out


def test_janus1982_hybrid_globals(capsys, tmp_path):
    """Global declarations + <=> swap accepted in janus1982 mode."""
    source = """
    ; Global variables
    i
    j
    procedure main
        i += 5
        j += 10
        i <=> j
    """
    path = tmp_path / "glob82.ja"
    path.write_text(textwrap.dedent(source))
    main(["--std", "janus1982", "-s", str(path)])
    out, _ = capsys.readouterr()
    assert "i = 10" in out
    assert "j = 5" in out


def test_janus1982_hybrid_read_write(capsys, tmp_path, monkeypatch):
    """read / write statements work."""
    source = """
    procedure main
        read x
        x += 1
        write x
    """
    path = tmp_path / "rw82.ja"
    path.write_text(textwrap.dedent(source))
    import io
    monkeypatch.setattr(sys, "stdin", io.StringIO("41\n"))
    main(["--std", "janus1982", str(path)])
    out, _ = capsys.readouterr()
    assert "42\n" in out


# ---------------------------------------------------------------------------
# Pure 1982 syntax tests
# ---------------------------------------------------------------------------

def test_1982_global_decl_and_write(capsys, tmp_path):
    """Global variable declaration + write."""
    source = """
    x
    procedure main
        x += 42
        write x
    """
    path = tmp_path / "t.ja"
    path.write_text(textwrap.dedent(source))
    assert main(["--std", "janus1982", str(path)]) == 0
    out, _ = capsys.readouterr()
    assert "42" in out


def test_1982_multi_globals_one_line(capsys, tmp_path):
    """Multiple globals declared on one line."""
    source = """
    a b c
    procedure main
        a += 1
        b += 2
        c += 3
        write a
        write b
        write c
    """
    path = tmp_path / "t.ja"
    path.write_text(textwrap.dedent(source))
    assert main(["--std", "janus1982", str(path)]) == 0
    out, _ = capsys.readouterr()
    assert "1" in out and "2" in out and "3" in out


def test_1982_swap_colon(capsys, tmp_path):
    """Colon operator swaps two variables."""
    source = """
    a
    b
    procedure main
        a += 10
        b += 20
        a : b
        write a
        write b
    """
    path = tmp_path / "t.ja"
    path.write_text(textwrap.dedent(source))
    assert main(["--std", "janus1982", str(path)]) == 0
    out, _ = capsys.readouterr()
    lines = out.strip().splitlines()
    assert lines[0] == "20"
    assert lines[1] == "10"


def test_1982_xor_update(capsys, tmp_path):
    """!= is the XOR-update operator (5 XOR 3 = 6)."""
    source = """
    x
    procedure main
        x += 5
        x != 3
        write x
    """
    path = tmp_path / "t.ja"
    path.write_text(textwrap.dedent(source))
    assert main(["--std", "janus1982", str(path)]) == 0
    out, _ = capsys.readouterr()
    assert "6" in out


def test_1982_hash_neq(capsys, tmp_path):
    """# is the not-equal comparison operator."""
    source = """
    x
    procedure main
        x += 1
        if x # 0
        then x += 9
        fi x # 0
        write x
    """
    path = tmp_path / "t.ja"
    path.write_text(textwrap.dedent(source))
    assert main(["--std", "janus1982", str(path)]) == 0
    out, _ = capsys.readouterr()
    assert "10" in out


def test_1982_backslash_mod(capsys, tmp_path):
    r"""\ is the integer remainder operator (17 mod 5 = 2)."""
    source = r"""
    x
    procedure main
        x += 17
        x -= 17 \ 5
        write x
    """
    path = tmp_path / "t.ja"
    path.write_text(textwrap.dedent(source))
    assert main(["--std", "janus1982", str(path)]) == 0
    out, _ = capsys.readouterr()
    assert "15" in out  # 17 - 2 = 15


def test_1982_call_no_parens(capsys, tmp_path):
    """call without parentheses invokes a procedure."""
    source = """
    x
    procedure add5
        x += 5
    procedure main
        call add5
        write x
    """
    path = tmp_path / "t.ja"
    path.write_text(textwrap.dedent(source))
    assert main(["--std", "janus1982", str(path)]) == 0
    out, _ = capsys.readouterr()
    assert "5" in out


def test_1982_uncall_reverses(capsys, tmp_path):
    """uncall executes a procedure in reverse.

    write is reversible (consumes the value), so snapshot x into y for
    output instead of writing x between call and uncall.
    """
    source = """
    x y
    procedure add3
        x += 3
    procedure main
        call add3
        y += x
        write y
        uncall add3
        write x
    """
    path = tmp_path / "t.ja"
    path.write_text(textwrap.dedent(source))
    assert main(["--std", "janus1982", str(path)]) == 0
    out, _ = capsys.readouterr()
    lines = out.strip().splitlines()
    assert lines[0] == "3"
    assert lines[1] == "0"


def test_1982_from_loop_until(capsys, tmp_path):
    """from/loop/until counts 0..n-1."""
    source = """
    n
    i
    procedure main
        n += 4
        from i=0
        loop i += 1
        until i=n
        i -= n
        write n
    """
    path = tmp_path / "t.ja"
    path.write_text(textwrap.dedent(source))
    assert main(["--std", "janus1982", str(path)]) == 0
    out, _ = capsys.readouterr()
    assert "4" in out


def test_1982_from_do_loop_until(capsys, tmp_path):
    """from/do/loop/until: do block runs each iteration before the until check."""
    source = """
    x
    i
    procedure main
        from i=0
        do x += 1
        loop i += 1
        until i=3
        i -= 3
        write x
    """
    path = tmp_path / "t.ja"
    path.write_text(textwrap.dedent(source))
    assert main(["--std", "janus1982", str(path)]) == 0
    out, _ = capsys.readouterr()
    assert "4" in out  # do runs 4 times (i=0,1,2,3; exits after i=3)


def test_1982_array_variable(capsys, tmp_path):
    """Array declaration and indexing."""
    source = """
    arr[5]
    procedure main
        arr[2] += 99
        write arr[2]
    """
    path = tmp_path / "t.ja"
    path.write_text(textwrap.dedent(source))
    assert main(["--std", "janus1982", str(path)]) == 0
    out, _ = capsys.readouterr()
    assert "99" in out


def test_1982_array_swap(capsys, tmp_path):
    """Colon swaps array elements."""
    source = """
    arr[3]
    procedure main
        arr[0] += 10
        arr[1] += 20
        arr[0] : arr[1]
        write arr[0]
        write arr[1]
    """
    path = tmp_path / "t.ja"
    path.write_text(textwrap.dedent(source))
    assert main(["--std", "janus1982", str(path)]) == 0
    out, _ = capsys.readouterr()
    lines = out.strip().splitlines()
    assert lines[0] == "20"
    assert lines[1] == "10"


def test_1982_multi_proc_global(capsys, tmp_path):
    """Multiple procedures share global variables."""
    source = """
    acc
    procedure add3
        acc += 3
    procedure add7
        acc += 7
    procedure main
        call add3
        call add7
        write acc
    """
    path = tmp_path / "t.ja"
    path.write_text(textwrap.dedent(source))
    assert main(["--std", "janus1982", str(path)]) == 0
    out, _ = capsys.readouterr()
    assert "10" in out


def test_1982_fib_global(capsys, tmp_path):
    """Fibonacci with pure global variables (1982 style, no parameters)."""
    source = """
    n
    x1
    x2
    procedure fib
        if n = 0
        then x1 += 1
             x2 += 1
        else n -= 1
             call fib
             x1 += x2
             x1 : x2
        fi x1 = x2
    procedure main
        n += 10
        call fib
        write x1
        write x2
    """
    path = tmp_path / "t.ja"
    path.write_text(textwrap.dedent(source))
    assert main(["--std", "janus1982", str(path)]) == 0
    out, _ = capsys.readouterr()
    lines = out.strip().splitlines()
    assert lines[0] == "89"   # fib(11)
    assert lines[1] == "144"  # fib(12)


def test_1982_counter_sum(capsys, tmp_path):
    """Sum 0+1+...+(n-1) using from/loop/until."""
    source = """
    n
    sum
    i
    procedure main
        n += 5
        from i=0
        loop sum += i
             i += 1
        until i=n
        i -= n
        write sum
    """
    path = tmp_path / "t.ja"
    path.write_text(textwrap.dedent(source))
    assert main(["--std", "janus1982", str(path)]) == 0
    out, _ = capsys.readouterr()
    assert "10" in out  # 0+1+2+3+4 = 10


def test_1982_sqrt(capsys, tmp_path):
    """Integer square root from the 1982 paper (sqrt(144) = 12)."""
    source = """
    num root   z bit
    procedure root
        bit += 1
        from bit=1
        loop call doublebit
        until (bit*bit) > num
        from (bit*bit) > num
        do   uncall doublebit
             if ((root+bit)*(root+bit)) <= num
             then root += bit
             fi ((root/bit) \\ 2) # 0
        until bit=1
        bit -= 1
        num -= root*root
    procedure doublebit
        z += bit
        bit += z
        z -= bit/2
    procedure main
        num += 144
        call root
        write root
        write num
    """
    path = tmp_path / "t.ja"
    path.write_text(textwrap.dedent(source))
    assert main(["--std", "janus1982", str(path)]) == 0
    out, _ = capsys.readouterr()
    lines = out.strip().splitlines()
    assert lines[0] == "12"
    assert lines[1] == "0"


def test_1982_factor_12(capsys, tmp_path):
    """Factorization from the 1982 paper: 12 = 2 * 2 * 3."""
    source = r"""
    num try z i
    fact[20]

    procedure factor
        from (try=0) & (num>1)
        loop call nexttry
             from fact[i] # try
             loop i += 1
                  fact[i] += try
                  z += num/try
                  z : num
                  z -= num*try
             until (num \ try) # 0
        until (try*try) > num

        if num # 1
        then i += 1
             fact[i] : num
        else num -= 1
        fi fact[i] # fact[i-1]

        if (fact[i-1]*fact[i-1]) < fact[i]
        then from (try*try) > fact[i]
             loop uncall nexttry
             until try=0
        else try -= fact[i-1]
        fi (fact[i-1]*fact[i-1]) < fact[i]

        call zeroi

    procedure zeroi
        from fact[i+1] = 0
        loop i -= 1
        until i = 0

    procedure nexttry
        try += 2
        if try = 4
        then try -= 1
        fi try = 3

    procedure main
        num += 12
        call factor
        write i
        write fact[1]
        write fact[2]
        write fact[3]
    """
    path = tmp_path / "t.ja"
    path.write_text(textwrap.dedent(source))
    assert main(["--std", "janus1982", str(path)]) == 0
    out, _ = capsys.readouterr()
    lines = out.strip().splitlines()
    # After factor+zeroi: i is zeroed out by zeroi; fact[1..3] hold the factors
    assert lines[0] == "0"   # i=0 (zeroi restored i to 0)
    assert lines[1] == "2"   # fact[1] = 2
    assert lines[2] == "2"   # fact[2] = 2  (12 = 2 * 2 * 3)
    assert lines[3] == "3"   # fact[3] = 3


def test_1982_sort_n3(capsys, tmp_path):
    """Bubble sort from the 1982 paper works correctly for n=3.
    NOTE: The original sort has a known bug for n>=4 (fi-condition
    'perm[j] > perm[j+1]' is inconsistent after first outer pass).
    """
    source = """
    list[12]
    perm[12]
    n i j

    procedure sort
        from i=0
        loop j += n-2
             from j=n-2
             loop if list[j] > list[j+1]
                       then list[j] : list[j+1]
                            perm[j] : perm[j+1]
                       fi perm[j] > perm[j+1]
                  j -= 1
             until j=i-1
             j -= i-1
             i += 1
        until i=n-1
        i -= n-1

    procedure makeidperm
        from i=0
        loop perm[i] += i
             i += 1
        until i=n
        i -= n

    procedure main
        n += 3
        list[0] += 30
        list[1] += 10
        list[2] += 20
        call makeidperm
        call sort
        write list[0]
        write list[1]
        write list[2]
    """
    path = tmp_path / "t.ja"
    path.write_text(textwrap.dedent(source))
    assert main(["--std", "janus1982", str(path)]) == 0
    out, _ = capsys.readouterr()
    lines = out.strip().splitlines()
    assert lines == ["10", "20", "30"]


# ---------------------------------------------------------------------------
# Reversible I/O (read/write per the 1982 paper)
# ---------------------------------------------------------------------------

def test_1982_write_clears_the_variable(capsys, tmp_path):
    """write emits the value and consumes it (clears back to zero)."""
    source = """
    x
    procedure main
        x += 42
        write x
        write x
    """
    path = tmp_path / "t.ja"
    path.write_text(textwrap.dedent(source))
    assert main(["--std", "janus1982", str(path)]) == 0
    out, _ = capsys.readouterr()
    assert out.strip().splitlines() == ["42", "0"]


def test_1982_read_requires_zero_target(capsys, tmp_path, monkeypatch):
    """read into a non-zero variable is an error."""
    import io
    source = """
    x
    procedure main
        x += 5
        read x
    """
    path = tmp_path / "t.ja"
    path.write_text(textwrap.dedent(source))
    monkeypatch.setattr(sys, "stdin", io.StringIO("1\n"))
    assert main(["--std", "janus1982", str(path)]) != 0
    out, _ = capsys.readouterr()
    assert "must be zero" in out


def test_1982_read_write_runs_backward(capsys, tmp_path, monkeypatch):
    """Backward execution turns read<->write: output 42 recovers input 41."""
    import io
    source = """
    x
    procedure main
        read x
        x += 1
        write x
    """
    path = tmp_path / "t.ja"
    path.write_text(textwrap.dedent(source))
    monkeypatch.setattr(sys, "stdin", io.StringIO("42\n"))
    assert main(["--std", "janus1982", "--direction", "backward", str(path)]) == 0
    out, _ = capsys.readouterr()
    assert "41\n" in out
