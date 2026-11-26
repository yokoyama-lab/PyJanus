"""Output / garbage annotations for Janus programs (see docs/output-annotation.md).

Janus has no notion of which end-state variables are *outputs*: the whole
final store is the result.  The RC-03 resource atlas therefore reports
``final_live_bits`` as a bare number and refuses to split it into "output"
and "garbage".  This module supplies the missing classification layer
without touching the parser or the runtime:

* :func:`parse_comment_annotations` reads structured comments
  (``// @out: a, K``, ``// @in: wt, val``, ``// @garbage: gb``,
  ``// @scratch: tmp``) from a program's source text.
* :func:`load_sidecar` / :func:`sidecar_for` read the hand-written sidecar
  ``tests/resource_atlas/annotations/out_annotations.json``.
* :func:`classify` maps the per-array end-state facts that the resource
  profiler emits (``puts``, ``takes``, ``ends_empty``, ``written``) plus an
  annotation to one of the four terminal classes
  ``output`` / ``input-preserved`` / ``garbage`` / ``clean``.

Everything here is string- and dict-level; nothing imports the AST.
"""
from __future__ import annotations

from dataclasses import dataclass, field
import json
from pathlib import Path
import re
from typing import Any, Iterable, Mapping

# Roles a variable can be given by an annotation.
ROLE_OUT = "output"
ROLE_IN = "input"
ROLE_GARBAGE = "garbage"
ROLE_SCRATCH = "scratch"
ROLES = (ROLE_OUT, ROLE_IN, ROLE_GARBAGE, ROLE_SCRATCH)

# Terminal classes produced by :func:`classify`.
CLASS_OUTPUT = "output"
CLASS_INPUT = "input-preserved"
CLASS_GARBAGE = "garbage"
CLASS_CLEAN = "clean"
CLASSES = (CLASS_OUTPUT, CLASS_INPUT, CLASS_GARBAGE, CLASS_CLEAN)

# Comment-tag spelling -> role.  ``@out``/``@output``, ``@in``/``@input`` are
# accepted so that the tags read naturally next to the proposed ``out``/``in``
# parameter qualifiers.
_TAG_ROLES = {
  "out": ROLE_OUT,
  "output": ROLE_OUT,
  "in": ROLE_IN,
  "input": ROLE_IN,
  "garbage": ROLE_GARBAGE,
  "gb": ROLE_GARBAGE,
  "scratch": ROLE_SCRATCH,
}

# ``// @out: a, K[]``  or  ``/* @in: wt val */`` (one tag per line).
_TAG_RE = re.compile(
  r"^\s*(?://|/\*|\*)\s*@(out|output|in|input|garbage|gb|scratch)\s*:\s*(?P<names>[^*\n]*?)\s*(?:\*/)?\s*$",
  re.IGNORECASE,
)
_NAME_SPLIT_RE = re.compile(r"[,\s]+")
_NAME_RE = re.compile(r"^[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*$")


@dataclass
class Annotation:
  """The roles a program assigns to its main-level variables.

  ``roles`` maps a variable name (array, scalar, stack or dotted struct
  field such as ``a.v``) to one of :data:`ROLES`.  ``source`` records where
  the annotation came from (``"comment"`` or ``"sidecar"``); ``file`` and
  ``confidence`` are carried through from the sidecar when present.
  """

  roles: dict[str, str] = field(default_factory=dict)
  source: str = "comment"
  file: str | None = None
  confidence: str | None = None
  rationale: str | None = None

  def role_of(self, name: str) -> str | None:
    return self.roles.get(name)

  def names_with(self, role: str) -> list[str]:
    return sorted(n for n, r in self.roles.items() if r == role)

  @property
  def outputs(self) -> list[str]:
    return self.names_with(ROLE_OUT)

  @property
  def inputs(self) -> list[str]:
    return self.names_with(ROLE_IN)

  def merged(self, other: "Annotation") -> "Annotation":
    """Return a copy where ``other``'s roles override ours (comment > sidecar)."""
    roles = dict(self.roles)
    roles.update(other.roles)
    return Annotation(
      roles=roles,
      source=f"{self.source}+{other.source}" if other.roles else self.source,
      file=self.file or other.file,
      confidence=other.confidence or self.confidence,
      rationale=other.rationale or self.rationale,
    )


class AnnotationError(ValueError):
  """Raised on a malformed annotation (bad name, conflicting roles)."""


# ---------------------------------------------------------------------------
# Structured comments
# ---------------------------------------------------------------------------

def _split_names(text: str) -> list[str]:
  names: list[str] = []
  for raw in _NAME_SPLIT_RE.split(text.strip()):
    if not raw:
      continue
    name = raw[:-2] if raw.endswith("[]") else raw
    if not _NAME_RE.match(name):
      raise AnnotationError(f"bad variable name in annotation: {raw!r}")
    names.append(name)
  return names


def parse_comment_annotations(source: str, *, strict: bool = True) -> Annotation:
  """Extract ``// @out:`` / ``// @in:`` / ``// @garbage:`` / ``// @scratch:`` tags.

  Tags may appear anywhere in the file (conventionally at the top of the
  file or at the top of ``main``); several tags of the same kind accumulate.
  A name given two different roles raises :class:`AnnotationError` when
  ``strict`` is true, otherwise the later tag wins.  Names may be dotted
  (``a.v``) for struct fields and may carry a trailing ``[]``.
  """
  roles: dict[str, str] = {}
  for lineno, line in enumerate(source.splitlines(), start=1):
    m = _TAG_RE.match(line)
    if not m:
      continue
    role = _TAG_ROLES[m.group(1).lower()]
    try:
      names = _split_names(m.group("names"))
    except AnnotationError as exc:
      raise AnnotationError(f"line {lineno}: {exc}") from None
    for name in names:
      prev = roles.get(name)
      if prev is not None and prev != role and strict:
        raise AnnotationError(
          f"line {lineno}: {name!r} annotated both {prev!r} and {role!r}"
        )
      roles[name] = role
  return Annotation(roles=roles, source="comment")


def has_comment_annotations(source: str) -> bool:
  return any(_TAG_RE.match(line) for line in source.splitlines())


# ---------------------------------------------------------------------------
# Sidecar JSON
# ---------------------------------------------------------------------------

DEFAULT_SIDECAR = (
  Path(__file__).resolve().parents[1]
  / "tests" / "resource_atlas" / "annotations" / "out_annotations.json"
)


def _normalize_role(value: str) -> str:
  """``"garbage (reversibility log)"`` -> ``"garbage"``; validate."""
  head = value.strip().split()[0].split("(")[0].lower() if value.strip() else ""
  role = _TAG_ROLES.get(head, head)
  if role not in ROLES:
    raise AnnotationError(f"unknown role {value!r}")
  return role


def annotation_from_entry(entry: Mapping[str, Any]) -> Annotation:
  """Build an :class:`Annotation` from one sidecar entry (see README)."""
  roles: dict[str, str] = {}
  for name, role in (entry.get("arrays") or {}).items():
    roles[name] = _normalize_role(role)
  for name, role in (entry.get("stacks") or {}).items():
    roles[name] = _normalize_role(role)
  for name in entry.get("scalars_out") or []:
    roles[name] = ROLE_OUT
  for name in entry.get("scalars_in") or []:
    roles.setdefault(name, ROLE_IN)
  return Annotation(
    roles=roles,
    source="sidecar",
    file=entry.get("file"),
    confidence=entry.get("confidence"),
    rationale=entry.get("rationale"),
  )


def load_sidecar(path: str | Path = DEFAULT_SIDECAR) -> dict[str, Annotation]:
  """Load the sidecar file; returns ``{relative_fixture_path: Annotation}``."""
  with open(path, "r", encoding="utf-8") as f:
    data = json.load(f)
  entries = data["programs"] if isinstance(data, dict) else data
  result: dict[str, Annotation] = {}
  for entry in entries:
    ann = annotation_from_entry(entry)
    if not ann.file:
      raise AnnotationError("sidecar entry without 'file'")
    if ann.file in result:
      raise AnnotationError(f"duplicate sidecar entry for {ann.file}")
    result[ann.file] = ann
  return result


def sidecar_for(
  file: str | Path,
  sidecar: Mapping[str, Annotation],
  *,
  prefer_dir: str = "tests/jana2014/fixtures/examples",
) -> Annotation | None:
  """Find the annotation for ``file``.

  ``file`` may be a repository-relative path (exact match), an absolute
  path (matched on its repo-relative suffix) or a bare basename.  Several
  fixtures share a basename (``fib.ja`` exists in three dialect corpora);
  a bare basename then resolves to the copy under ``prefer_dir``.
  """
  text = str(file).replace("\\", "/")
  if text in sidecar:
    return sidecar[text]
  suffix_matches = [k for k in sidecar if text.endswith("/" + k)]
  if len(suffix_matches) == 1:
    return sidecar[suffix_matches[0]]
  base = text.rsplit("/", 1)[-1]
  base_matches = [k for k in sidecar if k.rsplit("/", 1)[-1] == base]
  if len(base_matches) == 1:
    return sidecar[base_matches[0]]
  for k in base_matches:
    if k.startswith(prefer_dir):
      return sidecar[k]
  return None


def annotation_for_program(
  file: str | Path,
  source: str | None = None,
  sidecar: Mapping[str, Annotation] | None = None,
) -> Annotation:
  """Sidecar entry (if any) overridden by in-source comment tags (if any)."""
  base = Annotation(roles={}, source="none", file=str(file))
  if sidecar is not None:
    found = sidecar_for(file, sidecar)
    if found is not None:
      base = found
  if source is not None:
    comment = parse_comment_annotations(source)
    if comment.roles:
      return base.merged(comment)
  return base


# ---------------------------------------------------------------------------
# Classification of arrays at termination
# ---------------------------------------------------------------------------

@dataclass
class Classified:
  name: str
  cls: str                      # one of CLASSES
  role: str | None              # annotated role, None if unannotated
  puts: int
  takes: int
  ends_empty: bool
  written: bool
  note: str = ""                # mismatch / unannotated warnings


def _as_bool(v: Any) -> bool:
  if isinstance(v, str):
    return v.strip().lower() in {"1", "true", "yes", "y", "t"}
  return bool(v)


def _as_int(v: Any) -> int:
  if v is None or v == "":
    return 0
  return int(v)


def classify_one(name: str, state: Mapping[str, Any], role: str | None) -> Classified:
  """Classify a single array (see docs/output-annotation.md, 判定手続き).

  1. ``ends_empty`` (every cell 0 at termination) -> ``clean``, whatever the
     annotation says; an ``output``/``input`` annotation on a clean array is
     reported as a mismatch note, a ``scratch`` annotation is confirmed.
  2. otherwise the annotated role decides:
     ``output`` -> ``output``; ``input`` -> ``input-preserved``;
     ``garbage``/``scratch``/unannotated -> ``garbage``.  A ``scratch`` array
     that is not empty and an unannotated array get a note.
  """
  puts = _as_int(state.get("puts"))
  takes = _as_int(state.get("takes"))
  ends_empty = _as_bool(state.get("ends_empty"))
  written = _as_bool(state.get("written", puts > 0))
  note = ""
  if ends_empty:
    cls = CLASS_CLEAN
    if role in (ROLE_OUT, ROLE_IN):
      note = f"annotated {role} but all-zero at termination"
  elif role == ROLE_OUT:
    cls = CLASS_OUTPUT
  elif role == ROLE_IN:
    cls = CLASS_INPUT
    if takes > 0 or (written and puts > 0 and takes > 0):
      # Inputs are normally only initialised in main (puts only); a take on
      # an input means it was modified and restored (round trip) -- fine,
      # but worth a note so the recount can list it.
      note = "input array had takes (modified and restored?)"
  else:
    cls = CLASS_GARBAGE
    if role is None:
      note = "unannotated"
    elif role == ROLE_SCRATCH:
      note = "annotated scratch but non-zero at termination"
  return Classified(name, cls, role, puts, takes, ends_empty, written, note)


def classify(
  arrays_end_state: Mapping[str, Mapping[str, Any]],
  annotation: Annotation | Mapping[str, str] | None,
) -> dict[str, str]:
  """Map ``{array: {puts, takes, ends_empty, written}}`` to ``{array: class}``.

  ``annotation`` may be an :class:`Annotation` or a plain ``{name: role}``
  mapping (roles as in :data:`ROLES`); ``None`` means "nothing annotated"
  (every non-empty array is garbage, as in the unannotated RC-03 count).
  """
  return {c.name: c.cls for c in classify_detailed(arrays_end_state, annotation)}


def classify_detailed(
  arrays_end_state: Mapping[str, Mapping[str, Any]],
  annotation: Annotation | Mapping[str, str] | None,
) -> list[Classified]:
  if annotation is None:
    roles: Mapping[str, str] = {}
  elif isinstance(annotation, Annotation):
    roles = annotation.roles
  else:
    roles = {k: _normalize_role(v) for k, v in annotation.items()}
  out: list[Classified] = []
  for name in arrays_end_state:
    out.append(classify_one(name, arrays_end_state[name], roles.get(name)))
  return out


def summarize(classified: Iterable[Classified]) -> dict[str, Any]:
  """Aggregate counts in the shape of the RC-03 sentence.

  Returns ``written`` (arrays with ``written``), ``never_take`` (written and
  ``takes == 0``) split by class, ``ends_empty`` count, and ``by_class``.
  """
  items = list(classified)
  written = [c for c in items if c.written]
  never_take = [c for c in written if c.takes == 0]
  by_class = {cls: sum(1 for c in written if c.cls == cls) for cls in CLASSES}
  never_take_by_class = {cls: sum(1 for c in never_take if c.cls == cls) for cls in CLASSES}
  return {
    "arrays": len(items),
    "written": len(written),
    "never_take": len(never_take),
    "never_take_by_class": never_take_by_class,
    "ends_empty": sum(1 for c in written if c.ends_empty),
    "by_class": by_class,
    "unannotated": sum(1 for c in written if c.role is None),
    "mismatches": [(c.name, c.note) for c in written if c.note and c.note != "unannotated"],
  }


__all__ = [
  "Annotation", "AnnotationError", "Classified",
  "ROLES", "ROLE_OUT", "ROLE_IN", "ROLE_GARBAGE", "ROLE_SCRATCH",
  "CLASSES", "CLASS_OUTPUT", "CLASS_INPUT", "CLASS_GARBAGE", "CLASS_CLEAN",
  "DEFAULT_SIDECAR",
  "parse_comment_annotations", "has_comment_annotations",
  "load_sidecar", "sidecar_for", "annotation_from_entry", "annotation_for_program",
  "classify", "classify_one", "classify_detailed", "summarize",
]
