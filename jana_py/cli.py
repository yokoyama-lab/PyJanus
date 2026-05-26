from __future__ import annotations

import argparse
import dataclasses
import io
import json
import sys
from enum import Enum
import math
import signal

from .format import format_program
from .invert import invert_program
from .parser_janus2026 import parse_program
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
  parser = argparse.ArgumentParser(
    prog="pyjanus",
    add_help=False,
    description="Parse, run, transform, and inspect Janus/Jana programs.",
    epilog=(
      "examples:\n"
      "  pyjanus program.ja\n"
      "  pyjanus -a program.ja\n"
      "  pyjanus -i program.ja\n"
      "  pyjanus -c -h myheader.h program.ja\n"
      "  pyjanus -m32 program.ja\n"
      "  pyjanus -p 65537 program.ja\n"
      "  pyjanus --profile program.ja\n"
      "  pyjanus --inverse '{\"x\": 5, \"y\": 8}' program.ja\n"
      "  cat program.ja | pyjanus -\n"
      "  pyjanus program.ja 10 20            # positional args become stdin lines for scanf\n"
      "  echo 10 | pyjanus program.ja        # equivalent: stdin piped directly"
    ),
    formatter_class=argparse.RawDescriptionHelpFormatter,
  )
  parser.add_argument("--std", dest="std", choices=["janus2026", "jana2014", "jana2014basic", "janus1982", "janus1982ext"], default="janus2026", help="language standard: janus2026 (default, C-style), jana2014, jana2014basic, janus1982 (strict 1982), janus1982ext (1982 + extensions)")
  parser.add_argument("-a", action="store_true", dest="ast", help="print the parsed AST as JSON")
  parser.add_argument("-i", action="store_true", dest="invert", help="invert the program; print source unless combined with execution modes")
  parser.add_argument("-c", action="store_true", dest="c_code", help="emit generated C code instead of running the program")
  parser.add_argument("-h", dest="header", metavar="HEADER", help="header include path/name used with `-c` C code generation")
  parser.add_argument("-m", dest="mod_bits", metavar="BITS", help="run integer arithmetic modulo 2^BITS")
  parser.add_argument("-p", dest="mod_prime", metavar="PRIME", help="run integer arithmetic in the finite field of size PRIME")
  parser.add_argument("-t", dest="timeout", metavar="SECONDS", help="abort execution after SECONDS and exit with code 124")
  parser.add_argument("-d", action="store_true", dest="debug", help="run with debugger-style stepping output")
  parser.add_argument("-e", action="store_true", dest="debug_on_error", help="break into debug mode only when an error occurs")
  parser.add_argument("-s", "--store", action="store_true", dest="show_store", help="print the final store after normal execution")
  parser.add_argument("--circuit", action="store_true", dest="circuit", help="synthesize and print a reversible circuit")
  parser.add_argument("--profile", action="store_true", dest="profile", help="profile space usage and print a memory profile")
  parser.add_argument("--inverse", dest="inverse_store", default=None, metavar="JSON", help="compute an initial store from the given final store JSON")
  parser.add_argument("--help", action="help", default=argparse.SUPPRESS,
                      help="show this help message and exit")
  parser.add_argument("file", nargs="?", help="input file path, or `-` to read source from stdin")
  parser.add_argument("program_args", nargs="*", help="positional arguments fed to the program's scanf/read via stdin (one per line)")
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
    elif arg.startswith("-std="):
      normalized.extend(["--std", arg[5:]])
    else:
      normalized.append(arg)
  return normalized


def _parse_optional_int(value: str | None) -> int | None:
  return int(value) if value not in {None, ""} else None


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
  if args.file is None:
    parser.print_help()
    return 0
  try:
    validate_args(args)
  except Exception as exc:
    if isinstance(exc, JanaError) and (args.debug or args.debug_on_error):
      return 1
    print(str(exc))
    return 1
  if args.file == "-":
    text = sys.stdin.read()
  else:
    with open(args.file, "r", encoding="utf-8") as f:
      text = f.read()
  if args.program_args:
    if args.file == "-":
      print("error: cannot pass program args when reading source from stdin (`-`)", file=sys.stderr)
      return 1
    sys.stdin = io.StringIO("\n".join(args.program_args) + "\n")
  timeout_sec = int(args.timeout) if args.timeout not in {None, ""} else -1
  timeout_enabled = timeout_sec > 0
  try:
    preprocessed = preprocess_text(args.file, text)
    if timeout_enabled:
      signal.signal(signal.SIGALRM, _timeout_handler)
      signal.alarm(timeout_sec)
    if args.std == "jana2014":
      from .parser_jana2014 import parse_program as parse_program_jana
      program = parse_program_jana(args.file, preprocessed.text, preprocessed.line_origins)
    elif args.std == "jana2014basic":
      from .parser_jana2014basic import parse_program as parse_program_jana
      program = parse_program_jana(args.file, preprocessed.text, preprocessed.line_origins)
    elif args.std in ("janus1982", "janus1982ext"):
      if args.std == "janus1982":
        from .parser_janus1982 import parse_program as parse_program_1982
      else:
        from .parser_janus1982ext import parse_program as parse_program_1982
      program = parse_program_1982(args.file, preprocessed.text, preprocessed.line_origins)
    else:
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
        mod_bits = _parse_optional_int(args.mod_bits)
        mod_prime = _parse_optional_int(args.mod_prime)
        print(
          Runtime(
            program,
            mod_bits=mod_bits,
            mod_prime=mod_prime,
            debug=args.debug,
            debug_on_error=args.debug_on_error,
            std=args.std,
          ).run(show_store=args.show_store),
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
