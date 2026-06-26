"""Modular arithmetic modes `-m BITS` (two's-complement) and `-p PRIME` (field).

`test_mul_div` covers modular `*=` / `/=`; here we pin the wraparound of `+=` /
`-=` / `^=` and that reversibility (call; uncall = identity) still holds through
the wraparound.
"""
from __future__ import annotations

import copy
import textwrap

from jana_py.parser_jana2014 import parse_program
from jana_py.runtime import Runtime
from jana_py.validate import validate_program


def run_mod(source: str, mod_bits=None, mod_prime=None) -> dict:
  program = parse_program("m.ja", textwrap.dedent(source))
  validate_program(program)
  rt = Runtime(program, mod_bits=mod_bits, mod_prime=mod_prime)
  rt.run()
  return {k: copy.deepcopy(c.value) for k, c in rt._root_frame.vars.items()}


# ----- two's-complement wraparound under -m -------------------------------

def test_mod_bits_add_wraps_to_signed_min():
  # 8-bit signed range is [-128, 127]; 127 + 1 wraps to -128.
  assert run_mod("procedure main()\n    int x\n    x += 127\n    x += 1\n", mod_bits=8)["x"] == -128


def test_mod_bits_sub_wraps_to_signed_max():
  # -128 - 1 wraps to 127.
  assert run_mod("procedure main()\n    int x\n    x -= 128\n    x -= 1\n", mod_bits=8)["x"] == 127


def test_mod_bits_value_stays_in_signed_range():
  for v in run_mod("procedure main()\n    int x\n    int y\n    x += 200\n    y -= 200\n",
                   mod_bits=8).values():
    assert -128 <= v <= 127


def test_mod_bits_xor_stays_in_range():
  s = run_mod("procedure main()\n    int x\n    int y\n    x += 200\n    y += 50\n    x ^= y\n",
              mod_bits=8)
  assert -128 <= s["x"] <= 127


# ----- prime field under -p -----------------------------------------------

def test_mod_prime_add_wraps():
  assert run_mod("procedure main()\n    int x\n    x += 5\n    x += 4\n", mod_prime=7)["x"] == 2


def test_mod_prime_sub_wraps_nonnegative():
  s = run_mod("procedure main()\n    int x\n    x += 2\n    x -= 5\n", mod_prime=7)
  assert s["x"] == 4 and 0 <= s["x"] < 7        # (2-5) mod 7 = 4


# ----- reversibility survives the wraparound ------------------------------

PROG = (
    "procedure mix(int a)\n"
    "    a *= 3\n"           # odd factor: invertible mod 2^bits and mod prime
    "    a += 200\n"
    "procedure main()\n"
    "    int x\n"
    "    x += 100\n"
    "    call mix(x)\n"
    "    uncall mix(x)\n"
)


def test_mod_bits_reversibility():
  assert run_mod(PROG, mod_bits=8)["x"] == 100


def test_mod_prime_reversibility():
  assert run_mod(PROG, mod_prime=251)["x"] == 100
