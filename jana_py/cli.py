from __future__ import annotations

import argparse
import dataclasses
import json
import sys
from enum import Enum
import math
import signal

from .format import format_program
from .invert import invert_program
from .parser import parse_program
from .preprocess import preprocess_text
from .c_codegen import format_program as format_c_program
from .errors import JanaError
from .runtime import Runtime
from .validate import validate_program


class TimeoutAbort(Exception):
  pass


def _timeout_handler(signum, frame):
  raise TimeoutAbort()


def _to_jsonable(value):
  if dataclasses.is_dataclass(value):
    return {field.name: _to_jsonable(getattr(value, field.name)) for field in dataclasses.fields(value)}
  if isinstance(value, Enum):
    return value.value
  if isinstance(value, list):
    return [_to_jsonable(item) for item in value]
  if isinstance(value, dict):
    return {key: _to_jsonable(item) for key, item in value.items()}
  return value


def build_parser() -> argparse.ArgumentParser:
  parser = argparse.ArgumentParser(prog="jana-py", add_help=False)
  parser.add_argument("-a", action="store_true", dest="ast")
  parser.add_argument("-i", action="store_true", dest="invert")
  parser.add_argument("-c", action="store_true", dest="c_code")
  parser.add_argument("-h", dest="header")
  parser.add_argument("-m", dest="mod_bits")
  parser.add_argument("-p", dest="mod_prime")
  parser.add_argument("-t", dest="timeout")
  parser.add_argument("-d", action="store_true", dest="debug")
  parser.add_argument("-e", action="store_true", dest="debug_on_error")
  parser.add_argument("--circuit", action="store_true", dest="circuit")
  parser.add_argument("--profile", action="store_true", dest="profile")
  parser.add_argument("--inverse", dest="inverse_store", default=None)
  parser.add_argument("file")
  return parser


def normalize_argv(argv: list[str]) -> list[str]:
  normalized: list[str] = []
  for arg in argv:
    if arg.startswith("-m") and arg != "-m":
      normalized.extend(["-m", arg[2:]])
    elif arg.startswith("-p") and arg != "-p":
      normalized.extend(["-p", arg[2:]])
    elif arg.startswith("-t") and arg != "-t":
      normalized.extend(["-t", arg[2:]])
    elif arg.startswith("-h="):
      normalized.extend(["-h", arg[3:]])
    else:
      normalized.append(arg)
  return normalized


def validate_args(args) -> None:
  if args.mod_bits is not None and args.mod_bits != "":
    int(args.mod_bits)
  if args.mod_prime is not None and args.mod_prime != "":
    prime = int(args.mod_prime)
    if prime < 2 or any(prime % n == 0 for n in range(2, math.isqrt(prime) + 1)):
      raise ValueError("Non-prime given to -p option")
  if args.timeout is not None and args.timeout != "":
    int(args.timeout)


def main(argv: list[str] | None = None) -> int:
  parser = build_parser()
  args = parser.parse_args(normalize_argv(argv or sys.argv[1:]))
  try:
    validate_args(args)
  except Exception as exc:
    if isinstance(exc, JanaError) and (args.debug or args.debug_on_error):
      return 1
    print(str(exc))
    return 1
  text = sys.stdin.read() if args.file == "-" else open(args.file, "r", encoding="utf-8").read()
  timeout_sec = int(args.timeout) if args.timeout not in {None, ""} else -1
  timeout_enabled = timeout_sec > 0
  try:
    preprocessed = preprocess_text(args.file, text)
    if timeout_enabled:
      signal.signal(signal.SIGALRM, _timeout_handler)
      signal.alarm(timeout_sec)
    program = parse_program(args.file, preprocessed.text, preprocessed.line_origins)
    validate_program(program)
    if args.circuit:
      from .circuit import synthesize_program
      circuit = synthesize_program(program)
      print(circuit.to_text())
      return 0
    if args.profile:
      from .pebble import profile_space, format_profile
      profile = profile_space(program)
      print(format_profile(profile))
      return 0
    if args.inverse_store is not None:
      from .inverse import run_inverse
      final_store = json.loads(args.inverse_store)
      result = run_inverse(program, final_store)
      if not result.success:
        print(result.error)
        return 1
      print(json.dumps(result.initial_store))
      return 0
    if args.invert:
      program = invert_program(program)
    if args.ast:
      print(json.dumps(_to_jsonable(program), indent=2))
    elif args.c_code:
      print(format_c_program(args.header, program), end="")
    else:
      if args.invert:
        print(format_program(program), end="")
      else:
        mod_bits = int(args.mod_bits) if args.mod_bits not in {None, ""} else None
        mod_prime = int(args.mod_prime) if args.mod_prime not in {None, ""} else None
        print(
          Runtime(
            program,
            mod_bits=mod_bits,
            mod_prime=mod_prime,
            debug=args.debug,
            debug_on_error=args.debug_on_error,
          ).run(),
          end="",
        )
    return 0
  except TimeoutAbort:
    return 124
  except RecursionError:
    if timeout_enabled:
      return 124
    print("maximum recursion depth exceeded")
    return 1
  except Exception as exc:
    print(str(exc))
    return 1
  finally:
    if timeout_enabled:
      signal.alarm(0)


if __name__ == "__main__":
  raise SystemExit(main())
