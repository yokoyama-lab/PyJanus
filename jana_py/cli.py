from __future__ import annotations

import argparse
import dataclasses
import io
import json
import sys
from enum import Enum
import math
import signal

from .ast import ProcMain, Program
from .format import formatter_for_std
from .invert import invert_program, invert_proc_globally, invert_stmts
from .preprocess import preprocess_text
from .c_codegen import format_program as format_c_program
from .errors import JanaError, format_jana_error
from .runtime import Runtime
from .validate import validate_program


# `--std` dialect -> dotted parser module (each exposes the same
# `parse_program(filename, text, line_origins)`); the matching source
# formatter comes from `format.formatter_for_std`.
STD_PARSER_MODULES = {
  "janus2026": "parser_janus2026",
  "jana2014": "parser_jana2014",
  "jana2014basic": "parser_jana2014basic",
  "jana2014_in_out": "parser_jana2014_in_out",
  "janus1982": "parser_janus1982",
  "janus1982ext": "parser_janus1982ext",
}


def parse_for_std(std: str, filename: str, text: str, line_origins) -> Program:
  import importlib
  module = importlib.import_module(f".{STD_PARSER_MODULES[std]}", __package__)
  return module.parse_program(filename, text, line_origins)


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


def _invert_program_full(program: Program) -> Program:
  """Globally invert a whole program (main body + procedures) for backward run."""
  main = program.main
  inv_main = (
    ProcMain(main.vdecls, invert_stmts(main.stmts, global_mode=True), main.pos)
    if main is not None
    else None
  )
  inv_procs = [invert_proc_globally(proc) for proc in program.procs]
  return Program(inv_main, inv_procs, program.struct_defs)


def _check_expect(actual: str, expected: str) -> int:
  """Compare program output against an expected value (trailing newlines ignored)."""
  if actual.rstrip("\n") == expected.rstrip("\n"):
    print("OK")
    return 0
  print("MISMATCH")
  print(f"  expected: {expected.rstrip(chr(10))!r}")
  print(f"  actual:   {actual.rstrip(chr(10))!r}")
  return 1


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
  parser.add_argument("--std", dest="std", choices=["janus2026", "jana2014", "jana2014basic", "jana2014_in_out", "janus1982", "janus1982ext"], default="janus2026", help="language standard: janus2026 (default, C-style), jana2014, jana2014basic, jana2014_in_out (jana2014 + reversible read/write I/O), janus1982 (strict 1982), janus1982ext (1982 + extensions)")
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
  parser.add_argument("--no-main", action="store_true", dest="no_main", help="allow a library file without a main procedure (for -a/-c/-i and validation; cannot be executed)")
  parser.add_argument("-I", dest="include_dirs", metavar="DIR", action="append", default=[], help="add DIR to the `#include` search path (repeatable); the bundled standard library is always searched")
  parser.add_argument("--circuit", action="store_true", dest="circuit", help="synthesize and print a reversible circuit")
  parser.add_argument("--profile", action="store_true", dest="profile", help="profile space usage and print a memory profile")
  parser.add_argument("--inverse", dest="inverse_store", default=None, metavar="JSON", help="compute an initial store from the given final store JSON")
  parser.add_argument("--direction", dest="direction", choices=["forward", "backward"], default="forward", help="execution direction: forward (default) or backward (run the program inverted)")
  parser.add_argument("--expect", dest="expect", default=None, metavar="TEXT", help="compare program output against TEXT; exit 0 if equal, 1 otherwise")
  parser.add_argument("--expect-file", dest="expect_file", default=None, metavar="PATH", help="like --expect but read the expected output from PATH")
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


def _source_map(filename: str, text: str) -> dict[str, str]:
  sources = {filename: text}
  if filename not in {"", "-"}:
    try:
      from pathlib import Path
      sources[str(Path(filename).resolve())] = text
    except OSError:
      pass
  return sources


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
  phase = "preprocessing"
  try:
    from pathlib import Path as _Path
    preprocessed = preprocess_text(args.file, text, include_dirs=[_Path(d) for d in args.include_dirs], std=args.std)
    if timeout_enabled:
      signal.signal(signal.SIGALRM, _timeout_handler)
      signal.alarm(timeout_sec)
    phase = "parsing"
    program = parse_for_std(args.std, args.file, preprocessed.text, preprocessed.line_origins)
    phase = "validation"
    validate_program(program, require_main=not args.no_main)
    if args.circuit:
      phase = "circuit synthesis"
      from .circuit import synthesize_program
      circuit = synthesize_program(program)
      print(circuit.to_text())
      return 0
    if args.profile:
      phase = "profiling"
      from .pebble import profile_space, format_profile
      profile = profile_space(program)
      print(format_profile(profile))
      return 0
    if args.inverse_store is not None:
      phase = "inverse analysis"
      from .inverse import run_inverse
      final_store = json.loads(args.inverse_store)
      result = run_inverse(program, final_store)
      if not result.success:
        print(result.error)
        return 1
      print(json.dumps(result.initial_store))
      return 0
    if args.invert:
      phase = "inversion"
      program = invert_program(program)
    if args.ast:
      print(json.dumps(_to_jsonable(program), indent=2))
    elif args.c_code:
      print(format_c_program(args.header, program), end="")
    else:
      if args.invert:
        # Each dialect gets inverted source in its own surface syntax.
        print(formatter_for_std(args.std).format_program(program), end="")
      else:
        mod_bits = _parse_optional_int(args.mod_bits)
        mod_prime = _parse_optional_int(args.mod_prime)
        run_program = _invert_program_full(program) if args.direction == "backward" else program
        phase = "execution"
        output = Runtime(
          run_program,
          mod_bits=mod_bits,
          mod_prime=mod_prime,
          debug=args.debug,
          debug_on_error=args.debug_on_error,
          std=args.std,
        ).run(show_store=args.show_store)
        if args.expect is not None or args.expect_file is not None:
          if args.expect_file is not None:
            with open(args.expect_file, "r", encoding="utf-8") as f:
              expected = f.read()
          else:
            expected = args.expect
          return _check_expect(output, expected)
        print(output, end="")
    return 0
  except TimeoutAbort:
    return 124
  except RecursionError:
    if timeout_enabled:
      return 124
    print("maximum recursion depth exceeded")
    return 1
  except JanaError as exc:
    print(format_jana_error(
      exc,
      phase=phase,
      std=args.std,
      direction=args.direction,
      sources=_source_map(args.file, text),
    ))
    return 1
  except Exception as exc:
    print(str(exc))
    return 1
  finally:
    if timeout_enabled:
      signal.alarm(0)


if __name__ == "__main__":
  raise SystemExit(main())
