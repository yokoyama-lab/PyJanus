from __future__ import annotations

from dataclasses import dataclass, field

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
