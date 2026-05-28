from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path

from .ast import SourcePos


@dataclass
class JanaError(Exception):
  pos: SourcePos
  message: str
  details: list[str] = field(default_factory=list)
  contextual: bool = False

  def add_detail(self, detail: str, contextual: bool = True) -> "JanaError":
    return JanaError(self.pos, self.message, self.details + [detail], self.contextual or contextual)

  def __str__(self) -> str:
    if self.contextual:
      lines = [f"Error at line {self.pos.line}:"]
      lines.append(f"  {self.message}")
      for detail in self.details:
        if detail.startswith("  where "):
          lines.append("")
          for where_line in detail.split("\n"):
            stripped = where_line.strip()
            if stripped.startswith("where "):
              lines.append(f"  Where: {stripped[6:]}")
            elif stripped:
              lines.append(f"         {stripped}")
        elif detail.startswith("In "):
          lines.append(f"  {detail}")
        else:
          lines.append(f"  {detail.lstrip()}")
      return "\n".join(lines)
    if self.pos.filename and not self.pos.line and not self.pos.column:
      return f'File "{self.pos.filename}":\n    {self.message}'
    if self.pos.filename and self.pos.line and self.pos.column:
      return f'File "{self.pos.filename}" in line {self.pos.line}, column {self.pos.column}:\n    {self.message}'
    return f"Error:\n    {self.message}"


def format_jana_error(
  error: JanaError,
  *,
  phase: str,
  std: str | None = None,
  direction: str | None = None,
  sources: dict[str, str] | None = None,
) -> str:
  """Format an error with enough context for automated repair tools."""
  lines = [f"PyJanus {phase} error"]
  lines.append(_format_field("message", error.message))
  legacy = str(error)
  if legacy != error.message:
    lines.append(_format_field("legacy", legacy))
  location = _format_location(error.pos)
  if location:
    lines.append(f"  location: {location}")
  if std:
    lines.append(f"  std: {std}")
  if direction:
    lines.append(f"  direction: {direction}")

  excerpt = _source_excerpt(error.pos, sources or {})
  if excerpt:
    lines.extend(["", "Source:", *excerpt])

  if error.details:
    lines.extend(["", "Context:"])
    for detail in error.details:
      lines.extend(_indent_block(detail))

  hints = _fix_hints(error.message)
  if hints:
    lines.extend(["", "Fix hints:"])
    lines.extend(f"  - {hint}" for hint in hints)

  return "\n".join(lines)


def _format_field(name: str, value: str) -> str:
  value_lines = value.splitlines() or [""]
  first, rest = value_lines[0], value_lines[1:]
  lines = [f"  {name}: {first}"]
  lines.extend(f"{' ' * (len(name) + 4)}{line}" for line in rest)
  return "\n".join(lines)


def _format_location(pos: SourcePos) -> str:
  if pos.filename and pos.line and pos.column:
    return f"{pos.filename}:{pos.line}:{pos.column}"
  if pos.filename and pos.line:
    return f"{pos.filename}:{pos.line}"
  if pos.line:
    return f"line {pos.line}"
  if pos.filename:
    return pos.filename
  return ""


def _source_excerpt(pos: SourcePos, sources: dict[str, str]) -> list[str]:
  if pos.line <= 0:
    return []
  text = _source_text(pos.filename, sources)
  if text is None:
    return []
  source_lines = text.splitlines()
  if pos.line > len(source_lines):
    return []
  start = max(1, pos.line - 1)
  end = min(len(source_lines), pos.line + 1)
  width = len(str(end))
  lines: list[str] = []
  for line_no in range(start, end + 1):
    marker = ">" if line_no == pos.line else " "
    lines.append(f"  {marker} {line_no:>{width}} | {source_lines[line_no - 1]}")
    if line_no == pos.line and pos.column > 0:
      caret_column = max(pos.column, 1)
      lines.append(f"    {' ' * width} | {' ' * (caret_column - 1)}^")
  return lines


def _source_text(filename: str, sources: dict[str, str]) -> str | None:
  if filename in sources:
    return sources[filename]
  if filename:
    try:
      resolved = str(Path(filename).resolve())
    except OSError:
      resolved = filename
    if resolved in sources:
      return sources[resolved]
    try:
      path = Path(filename)
      if path.is_file():
        return path.read_text(encoding="utf-8")
    except OSError:
      return None
  return None


def _indent_block(text: str) -> list[str]:
  return [f"  {line}" if line else "" for line in text.splitlines()]


def _fix_hints(message: str) -> list[str]:
  lower = message.lower()
  hints: list[str] = []
  if "`read` target" in message and "must be zero" in message:
    hints.extend([
      "In jana2014_in_out, `read x` is reversible only when `x` is zero before the read.",
      "Initialize the target to 0, clear it before `read`, or read into a fresh variable.",
    ])
  if "read reached end of input" in lower:
    hints.append("Provide one input value for each executed `read` statement, in execution order.")
  if "read expected an integer" in lower:
    hints.append("Pass integer input values only; each command-line program argument becomes one input line.")
  if "array index" in lower and "out of bounds" in lower:
    hints.append("Check the array size and the expression used as the index at this location.")
  if "has not been declared" in lower:
    hints.append("Declare the variable before use, or check for a spelling mismatch in the identifier.")
  if "procedure" in lower and "is not defined" in lower:
    hints.append("Define the procedure before running, or check the call/uncall procedure name.")
  if "unexpected" in lower and "expecting" in lower:
    hints.append("This is a parse error; inspect the highlighted token and add the expected syntax nearby.")
  if "assertion failed" in lower:
    hints.append("The reversible control-flow assertion did not hold; check the matching entry/exit condition.")
  if "division by zero" in lower:
    hints.append("Ensure the divisor expression is non-zero before executing this operation.")
  return hints
