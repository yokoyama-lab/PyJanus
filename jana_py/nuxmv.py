"""Run nuXmv on a model produced by `jana_py.smv` and read back the verdict.

The only property this driver cares about is an `INVARSPEC`, checked with
nuXmv's IC3 over the SMT (infinite-state) engine, so the answers are:

* ``proved``      — IC3 found an inductive invariant.  For the ERR location this
                    means *no input whatsoever* makes an assertion fail.
* ``refuted``     — IC3 returned a counterexample; the trace's first state is the
                    offending initial store, which PyJanus can replay directly.
* ``unknown``     — the solver gave up, timed out, or refused the model.

nuXmv is not a dependency of PyJanus: `find_nuxmv` returns ``None`` when it is
absent and every caller is expected to skip rather than fail.
"""

from __future__ import annotations

import os
import re
import shutil
import subprocess
import tempfile
from dataclasses import dataclass, field
from pathlib import Path

_DEFAULT_PATHS = [
    Path.home() / "dev" / "infra" / "tools" / "nuXmv",
]

_VERDICT_RE = re.compile(r"^-- invariant (?P<prop>.*?)\s+is (?P<verdict>true|false)\s*$")
#: nuXmv's own complaints about the *model*, as opposed to a verdict on it.
_MALFORMED_RE = re.compile(
    r"syntax error|TYPE ERROR|A model must be read before|"
    r"impossible to build|Parsing error", re.I)

#: Array cells are printed element-wise (`d[0] = 3`), and they are the part of
#: the store worth reading: under `--init any` the counterexample is the missing
#: precondition, and for an array program the precondition lives in the array.
_ASSIGN_RE = re.compile(
    r"^\s{4}(?P<name>[A-Za-z_][A-Za-z0-9_$#-]*(?:\[-?\d+\])*) = (?P<value>-?\d+)\s*$")


@dataclass
class Verdict:
  """The outcome for one `INVARSPEC`."""

  prop: str
  status: str  # "proved" | "refuted" | "unknown"
  counterexample: dict[str, int] = field(default_factory=dict)


@dataclass
class Result:
  verdicts: list[Verdict]
  output: str
  timed_out: bool = False
  #: nuXmv could not *read* the model.  Distinguished from `unknown` because a
  #: broken question is not a hard question: two corpus programs sat at
  #: `unknown` for having a variable named `K` or `T` (nuXmv reserves both),
  #: and nothing distinguished them from a genuine timeout.
  malformed: bool = False

  def status_of(self, prop_substring: str) -> str | None:
    """The verdict for one property, by a substring of its text.

    `status` below deliberately collapses everything to the weakest, which is
    right when every property means the same kind of thing.  The stack and
    inlining bounds broke that: `pc != BOUND` being refuted says the model hit
    its depth, not that the program fails, and reporting both as `refuted`
    turns a modelling limit into an accusation.  Callers that emit a verdict to
    a human ask for the properties separately.
    """
    if self.malformed or self.timed_out:
      return None
    hits = [v for v in self.verdicts if prop_substring in v.prop]
    if not hits:
      return None
    for want in ("refuted", "unknown", "proved"):
      if any(v.status == want for v in hits):
        return want
    return None

  @property
  def status(self) -> str:
    """The weakest status across all properties."""
    if self.malformed:
      return "model-error"
    if self.timed_out or not self.verdicts:
      return "unknown"
    for want in ("refuted", "unknown"):
      if any(v.status == want for v in self.verdicts):
        return want
    return "proved"


def find_nuxmv() -> Path | None:
  env = os.environ.get("NUXMV")
  if env and Path(env).exists():
    return Path(env)
  for candidate in _DEFAULT_PATHS:
    if candidate.exists():
      return candidate
  found = shutil.which("nuXmv")
  return Path(found) if found else None


def _environment(binary: Path) -> dict[str, str]:
  env = dict(os.environ)
  libs = binary.parent / "nuxmv-libs"
  if libs.is_dir():
    existing = env.get("LD_LIBRARY_PATH")
    env["LD_LIBRARY_PATH"] = f"{libs}:{existing}" if existing else str(libs)
  return env


def _parse(output: str) -> list[Verdict]:
  verdicts: list[Verdict] = []
  lines = output.splitlines()
  for index, line in enumerate(lines):
    match = _VERDICT_RE.match(line)
    if match is None:
      continue
    if match.group("verdict") == "true":
      verdicts.append(Verdict(match.group("prop"), "proved"))
      continue
    store: dict[str, int] = {}
    for follow in lines[index + 1:]:
      if follow.startswith("-- invariant") or follow.startswith("nuXmv >"):
        break
      assign = _ASSIGN_RE.match(follow)
      if assign and assign.group("name") != "pc":
        store.setdefault(assign.group("name"), int(assign.group("value")))
    verdicts.append(Verdict(match.group("prop"), "refuted", store))
  return verdicts


def check(model: str, *, timeout: float = 60.0, binary: Path | None = None) -> Result:
  """Check every `INVARSPEC` in `model` with IC3 and return the verdicts."""
  binary = binary or find_nuxmv()
  if binary is None:
    raise FileNotFoundError("nuXmv not found; set $NUXMV")
  with tempfile.TemporaryDirectory() as tmp:
    path = Path(tmp) / "model.smv"
    path.write_text(model, encoding="utf-8")
    script = f"read_model -i {path}\ngo_msat\ncheck_invar_ic3\nquit\n"
    try:
      proc = subprocess.run([str(binary), "-int"], input=script, capture_output=True,
                            text=True, timeout=timeout, env=_environment(binary))
    except subprocess.TimeoutExpired:
      return Result([], "", timed_out=True)
  output = proc.stdout + proc.stderr
  verdicts = _parse(output)
  # Only when nothing was decided: a well-formed run never prints these, and
  # tying the flag to an empty verdict list keeps a stray message in a trace
  # from masking real results.
  malformed = not verdicts and bool(_MALFORMED_RE.search(output))
  return Result(verdicts, output, malformed=malformed)
