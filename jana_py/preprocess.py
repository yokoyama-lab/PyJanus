from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import re

from .ast import SourcePos
from .errors import JanaError

# Supported: object-like macros, function-like macros, #undef, and #include "..."
# Supported conditionals: #ifdef, #ifndef, #else, #endif
# Not supported: #elif, variadics, #, ##, and system includes.
# Include placement: only the file-leading preamble may contain #include.

DEFINE_RE = re.compile(r"^(\s*)#define\s+([A-Za-z][A-Za-z0-9_']*)\s+(.*?)\s*$")
FUNCTION_DEFINE_RE = re.compile(r"^(\s*)#define\s+([A-Za-z][A-Za-z0-9_']*)\((.*?)\)\s*(.*?)\s*$")
UNDEF_RE = re.compile(r"^(\s*)#undef\s+([A-Za-z][A-Za-z0-9_']*)\s*$")
INCLUDE_RE = re.compile(r'^\s*#include\s+"([^"]+)"\s*$')
IFDEF_RE = re.compile(r"^\s*#ifdef\s+([A-Za-z][A-Za-z0-9_']*)\s*$")
IFNDEF_RE = re.compile(r"^\s*#ifndef\s+([A-Za-z][A-Za-z0-9_']*)\s*$")
ELSE_RE = re.compile(r"^\s*#else\s*$")
ENDIF_RE = re.compile(r"^\s*#endif\s*$")
DIRECTIVE_RE = re.compile(r"^\s*#")


@dataclass(frozen=True)
class LineOrigin:
  filename: str
  line: int


@dataclass(frozen=True)
class PreprocessedText:
  text: str
  line_origins: list[LineOrigin]


@dataclass(frozen=True)
class FunctionMacro:
  params: list[str]
  body: str


@dataclass
class ConditionalFrame:
  parent_active: bool
  current_active: bool
  branch_taken: bool
  seen_else: bool = False


def preprocess_text(filename: str, text: str) -> PreprocessedText:
  current_path = Path(filename).resolve() if filename not in {"", "-"} else None
  include_stack = [current_path] if current_path is not None else []
  return _preprocess_text(filename, text, {}, {}, include_stack)


def _preprocess_text(
  filename: str,
  text: str,
  macros: dict[str, str],
  function_macros: dict[str, FunctionMacro],
  include_stack: list[Path],
) -> PreprocessedText:
  out_lines: list[str] = []
  line_origins: list[LineOrigin] = []
  in_block_comment = False
  current_path = Path(filename).resolve() if filename not in {"", "-"} else None
  in_preamble = True
  conditional_stack: list[ConditionalFrame] = []

  logical_lines = _join_continued_lines(text)
  for lineno, body, newline_count in logical_lines:
    ifdef_match = IFDEF_RE.match(body)
    if ifdef_match:
      name = ifdef_match.group(1)
      parent_active = _is_active(conditional_stack)
      defined = name in macros or name in function_macros
      conditional_stack.append(ConditionalFrame(parent_active, parent_active and defined, defined))
      continue
    ifndef_match = IFNDEF_RE.match(body)
    if ifndef_match:
      name = ifndef_match.group(1)
      parent_active = _is_active(conditional_stack)
      defined = name in macros or name in function_macros
      conditional_stack.append(ConditionalFrame(parent_active, parent_active and not defined, not defined))
      continue
    if ELSE_RE.match(body):
      if not conditional_stack:
        raise JanaError(SourcePos(filename, lineno, 1), "Unexpected #else without matching #ifdef or #ifndef")
      frame = conditional_stack[-1]
      if frame.seen_else:
        raise JanaError(SourcePos(filename, lineno, 1), "Duplicate #else for conditional block")
      frame.seen_else = True
      frame.current_active = frame.parent_active and not frame.branch_taken
      frame.branch_taken = True
      continue
    if ENDIF_RE.match(body):
      if not conditional_stack:
        raise JanaError(SourcePos(filename, lineno, 1), "Unexpected #endif without matching #ifdef or #ifndef")
      conditional_stack.pop()
      continue

    if not _is_active(conditional_stack):
      continue

    stripped = body.strip()
    if in_preamble and stripped and not _is_comment_only_line(stripped):
      if not (
        FUNCTION_DEFINE_RE.match(body)
        or DEFINE_RE.match(body)
        or UNDEF_RE.match(body)
        or INCLUDE_RE.match(body)
        or IFDEF_RE.match(body)
        or IFNDEF_RE.match(body)
        or ELSE_RE.match(body)
        or ENDIF_RE.match(body)
      ):
        in_preamble = False
    if not in_block_comment:
      function_define_match = FUNCTION_DEFINE_RE.match(body)
      if function_define_match:
        _, name, params_text, replacement = function_define_match.groups()
        params = [param.strip() for param in params_text.split(",")] if params_text.strip() else []
        if any(not param for param in params):
          raise JanaError(SourcePos(filename, lineno, 1), f"Invalid macro parameter list for `{name}`")
        function_macros[name] = FunctionMacro(params, replacement)
        macros.pop(name, None)
        continue
      define_match = DEFINE_RE.match(body)
      if define_match:
        _, name, replacement = define_match.groups()
        macros[name] = _expand_macro_text(replacement, macros, function_macros, {name})
        function_macros.pop(name, None)
        continue
      undef_match = UNDEF_RE.match(body)
      if undef_match:
        _, name = undef_match.groups()
        macros.pop(name, None)
        function_macros.pop(name, None)
        continue
      include_match = INCLUDE_RE.match(body)
      if include_match:
        if not in_preamble:
          raise JanaError(SourcePos(filename, lineno, 1), '#include is only allowed in the file-leading declaration preamble')
        include_target = include_match.group(1)
        if current_path is None:
          raise JanaError(SourcePos(filename, lineno, 1), f'Cannot resolve include from stdin: "{include_target}"')
        include_path = (current_path.parent / include_target).resolve()
        if include_path in include_stack:
          chain = " -> ".join(str(path) for path in include_stack + [include_path])
          raise JanaError(SourcePos(filename, lineno, 1), f"Cyclic include detected: {chain}")
        if not include_path.exists():
          raise JanaError(SourcePos(filename, lineno, 1), f'Included file not found: "{include_target}"')
        included_text = include_path.read_text(encoding="utf-8")
        included = _preprocess_text(str(include_path), included_text, macros, function_macros, include_stack + [include_path])
        if included.text:
          out_lines.append(included.text)
          line_origins.extend(included.line_origins)
        continue
      if DIRECTIVE_RE.match(body):
        raise JanaError(SourcePos(filename, lineno, 1), f"Unsupported preprocessor directive: {body.strip()}")

    expanded, in_block_comment = _expand_line(body, macros, function_macros, in_block_comment)
    if newline_count == 0:
      out_lines.append(expanded)
      line_origins.append(LineOrigin(filename, lineno))
      continue
    out_lines.append(expanded + "\n")
    line_origins.append(LineOrigin(filename, lineno))
    for offset in range(1, newline_count):
      out_lines.append("\n")
      line_origins.append(LineOrigin(filename, lineno + offset))

  if conditional_stack:
    raise JanaError(SourcePos(filename, logical_lines[-1][0] if logical_lines else 1, 1), "Unterminated conditional block")
  return PreprocessedText("".join(out_lines), line_origins)


def _expand_line(line: str, macros: dict[str, str], function_macros: dict[str, FunctionMacro], in_block_comment: bool) -> tuple[str, bool]:
  out: list[str] = []
  i = 0
  while i < len(line):
    if in_block_comment:
      end = line.find("*/", i)
      if end == -1:
        out.append(line[i:])
        return "".join(out), True
      out.append(line[i:end + 2])
      i = end + 2
      in_block_comment = False
      continue

    if line.startswith("/*", i):
      out.append("/*")
      i += 2
      in_block_comment = True
      continue
    if line.startswith("//", i):
      out.append(line[i:])
      break
    if line[i] == '"':
      literal, end = _consume_string(line, i)
      out.append(literal)
      i = end
      continue
    if _is_ident_start(line[i]):
      start = i
      i += 1
      while i < len(line) and _is_ident_continue(line[i]):
        i += 1
      ident = line[start:i]
      func_result = _expand_function_macro(line, i, ident, macros, function_macros, set())
      if func_result is not None:
        replacement, end = func_result
        out.append(replacement)
        i = end
        continue
      out.append(_expand_macro_text(macros.get(ident, ident), macros, function_macros, {ident}))
      continue
    out.append(line[i])
    i += 1
  return "".join(out), in_block_comment


def _join_continued_lines(text: str) -> list[tuple[int, str, int]]:
  lines = text.splitlines(keepends=True)
  logical_lines: list[tuple[int, str, int]] = []
  i = 0
  while i < len(lines):
    start_lineno = i + 1
    current = lines[i]
    body = current[:-1] if current.endswith("\n") else current
    newline_count = 1 if current.endswith("\n") else 0
    while body.endswith("\\"):
      body = body[:-1]
      i += 1
      if i >= len(lines):
        break
      current = lines[i]
      part = current[:-1] if current.endswith("\n") else current
      body += part
      if current.endswith("\n"):
        newline_count += 1
    logical_lines.append((start_lineno, body, newline_count))
    i += 1
  return logical_lines


def _expand_macro_text(text: str, macros: dict[str, str], function_macros: dict[str, FunctionMacro], seen: set[str]) -> str:
  out: list[str] = []
  i = 0
  while i < len(text):
    if _is_ident_start(text[i]):
      start = i
      i += 1
      while i < len(text) and _is_ident_continue(text[i]):
        i += 1
      ident = text[start:i]
      if ident in seen:
        out.append(ident)
        continue
      func_result = _expand_function_macro(text, i, ident, macros, function_macros, seen)
      if func_result is not None:
        rendered, end = func_result
        out.append(rendered)
        i = end
        continue
      replacement = macros.get(ident)
      if replacement is None:
        out.append(ident)
      else:
        out.append(_expand_macro_text(replacement, macros, function_macros, seen | {ident}))
      continue
    out.append(text[i])
    i += 1
  return "".join(out)


def _expand_function_macro(
  text: str,
  index_after_ident: int,
  ident: str,
  macros: dict[str, str],
  function_macros: dict[str, FunctionMacro],
  seen: set[str],
) -> tuple[str, int] | None:
  macro = function_macros.get(ident)
  if macro is None or ident in seen:
    return None
  call = _parse_macro_call(text, index_after_ident)
  if call is None:
    return None
  args, end = call
  if len(args) != len(macro.params):
    return None
  expanded_args = {
    param: _expand_macro_text(arg.strip(), macros, function_macros, set())
    for param, arg in zip(macro.params, args)
  }
  substituted = _substitute_macro_params(macro.body, expanded_args)
  return _expand_macro_text(substituted, macros, function_macros, seen | {ident}), end


def _parse_macro_call(text: str, index: int) -> tuple[list[str], int] | None:
  i = index
  while i < len(text) and text[i].isspace():
    i += 1
  if i >= len(text) or text[i] != "(":
    return None
  i += 1
  depth = 1
  current: list[str] = []
  args: list[str] = []
  while i < len(text):
    char = text[i]
    if char == '"':
      literal, end = _consume_string(text, i)
      current.append(literal)
      i = end
      continue
    if char == "(":
      depth += 1
      current.append(char)
      i += 1
      continue
    if char == ")":
      depth -= 1
      if depth == 0:
        args.append("".join(current))
        return args if args != [""] else [], i + 1
      current.append(char)
      i += 1
      continue
    if char == "," and depth == 1:
      args.append("".join(current))
      current = []
      i += 1
      continue
    current.append(char)
    i += 1
  return None


def _substitute_macro_params(body: str, args: dict[str, str]) -> str:
  out: list[str] = []
  i = 0
  while i < len(body):
    if _is_ident_start(body[i]):
      start = i
      i += 1
      while i < len(body) and _is_ident_continue(body[i]):
        i += 1
      ident = body[start:i]
      out.append(args.get(ident, ident))
      continue
    out.append(body[i])
    i += 1
  return "".join(out)


def _consume_string(line: str, start: int) -> tuple[str, int]:
  i = start + 1
  while i < len(line):
    if line[i] == "\\":
      i += 2
      continue
    if line[i] == '"':
      return line[start:i + 1], i + 1
    i += 1
  return line[start:], len(line)


def _is_ident_start(char: str) -> bool:
  return char.isalpha()


def _is_ident_continue(char: str) -> bool:
  return char.isalnum() or char in {"_", "'"}


def _is_comment_only_line(stripped: str) -> bool:
  return stripped.startswith("//") or stripped.startswith("/*") or stripped == "*/"


def _is_active(conditional_stack: list[ConditionalFrame]) -> bool:
  return conditional_stack[-1].current_active if conditional_stack else True
