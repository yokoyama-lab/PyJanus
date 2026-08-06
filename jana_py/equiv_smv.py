"""Prove two Janus programs equivalent by deciding `P; Q†` against the identity.

`equiv.py` answers the same question by *running* both programs on a bounded
box of inputs.  This module answers it by **proof**: it builds the single
program `P; Q†` — `Q†` is Janus's syntactic inversion, so no self-composition
and no product construction is needed — compiles it with `smv.py`, and asks
nuXmv's IC3 whether that program is the identity on **every** store, over
unbounded integers.

Why the inverse instead of a product.  Comparing `P` and `Q` directly needs two
copies of the store and a model twice the size.  Reversibility gives a cheaper
route: `P ≡ Q` iff `P; Q†` is the identity where it is defined, and `P` and `Q`
have the same domain.  One store, one program counter.

What a full proof means.  Three `INVARSPEC`s are decided together:

* ``pc != ERR``    — no Janus assertion in `P; Q†` can fail, on any input.
* ``pc != BOUND``  — no run hits the procedure-inlining bound (emitted only when
  the bound is reachable at all).
* ``pc = FINAL -> interface unchanged`` — this module's addition.

If all three are proved then for every store σ the composed program terminates
and returns σ.  Hence `P` is total, `P(σ)` lies in the domain of `Q†`, and
`Q†(P(σ)) = σ`.  Applying `Q` — which is the inverse of `Q†` on that domain,
because Janus inversion is semantically the inverse — gives `Q(σ) = P(σ)`.
So **all three proved ⟹ `P` and `Q` are total and compute the same function**.

Anything weaker is reported as it stands: a refuted identity spec carries the
counterexample store, which is a concrete input on which the two programs
differ, and `unknown` stays `unknown`.

Three things this checker refuses rather than approximate:

* **A renamed interface variable.**  `smv.py` renames a Janus variable that
  collides with an nuXmv keyword (`K`, `T`, …), and this module does not track
  the renaming.  Every interface variable must appear verbatim in the emitted
  `VAR` block or the request is refused — otherwise the identity spec would
  quietly constrain nothing.
* **A different interface.**  The two programs must declare the same `main`
  variables, in the same order, with the same types.  Comparing programs with
  different interfaces is a different question and needs a stated
  correspondence.
* **A clashing procedure.**  `P` and `Q` are inlined into one model, so a
  procedure name defined by both must have the same body; otherwise one
  definition would silently win.

Note that only the **interface** — `main`'s declared variables — is compared.
Ancillas introduced by `local`/`delocal` also become model variables, but their
values at the end are none of the caller's business (Janus already obliges them
to be restored at `delocal`), and comparing them against an unconstrained
initial value would refute every correct program.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field, replace

from .ast import Program
from .format import format_proc, format_struct_def, format_vdecl
from .invert import invert_stmts
from .nuxmv import Result, check
from .smv import SmvUnsupported, compile_to_smv

#: `smv.py` writes this line to say which locations are the entry and the
#: normal exit.  The identity property is about the exit, so it has to be read
#: back out; a change to that comment must break this module loudly, not
#: silently produce a spec about the wrong location.
_FINAL_RE = re.compile(
    r"^-- pc = (?P<entry>\d+) : entry,\s+pc = (?P<final>\d+) : normal termination\s*$",
    re.M)

_NAME = r"[A-Za-z_][A-Za-z0-9_$#-]*"
_SCALAR_RE = re.compile(rf"^  (?P<name>{_NAME}) : integer;$", re.M)
_ARRAY_RE = re.compile(
    rf"^  (?P<name>{_NAME}) : array 0\.\.(?P<hi>\d+) of integer;$", re.M)

#: Suffix for the frozen copy of an interface variable.  Checked for freshness
#: against the model's own names before use.
_FROZEN_SUFFIX = "__at_entry"


@dataclass
class EquivModel:
  """The emitted model plus what the caller needs to read a verdict."""

  model: str
  #: `INVARSPEC` text of the identity property, so a verdict can be matched to it.
  identity_prop: str
  #: Interface variables actually compared, in declaration order.
  compared: tuple[str, ...] = ()


@dataclass
class EquivVerdict:
  """The outcome of `check_equivalence_smv`.

  The two halves of `P ≡ Q ⟺ P;Q† ⊑ id ∧ dom P = dom Q` are reported
  separately, because they fail for different reasons and only one of them is
  a statement that the programs disagree:

  * `identity` decides `P;Q† ⊑ id` — the runs that complete are the identity.
  * `totality` decides `pc != ERR` (and `pc != BOUND` when present) — every run
    completes.  Refuting it means some input drives `P;Q†` into a failed
    assertion, i.e. `P`'s output leaves `Q`'s range (or `P` itself is partial),
    so the *domains* differ even if the completing runs agree.

  Collapsing the two would report "different" for a pair that agrees wherever
  both are defined, which is the interesting case for a compiler pass that
  narrows a domain.
  """

  #: "equivalent" | "different" | "partial" | "unknown" | "model-error"
  status: str
  #: Store on which the two programs differ, when `status == "different"`.
  counterexample: dict[str, int] = field(default_factory=dict)
  #: Verdict on `P;Q† ⊑ id`: "proved" | "refuted" | "unknown".
  identity: str = "unknown"
  #: Weakest verdict across the ERR (and BOUND) properties.
  totality: str = "unknown"
  #: Per-property verdicts, straight from the driver.
  result: Result | None = None

  @property
  def proved_equivalent(self) -> bool:
    return self.status == "equivalent"


def _interface(program: Program) -> tuple[str, ...]:
  """`main`'s declarations, rendered without initializers.

  Initializers are dropped because equivalence is asked over the whole input
  domain: two programs that differ only in what they start their inputs at
  still compute the same function.
  """
  if program.main is None:
    raise SmvUnsupported("the program has no main procedure")
  return tuple(format_vdecl(v, allow_init=False) for v in program.main.vdecls)


def _merged_procs(prog_a: Program, prog_b: Program) -> list:
  """Procedures of both programs, refusing a name defined differently by each.

  Keyed on the *string*: `Proc.procname` is an `Ident` carrying a `SourcePos`,
  so keying on it would make the same procedure declared at two different lines
  compare unequal and the clash go undetected — exactly the case that matters,
  since the two programs are different files.
  """
  by_name = {p.procname.name: p for p in prog_a.procs}
  merged = list(prog_a.procs)
  for proc in prog_b.procs:
    existing = by_name.get(proc.procname.name)
    if existing is None:
      by_name[proc.procname.name] = proc
      merged.append(proc)
      continue
    if format_proc(existing) != format_proc(proc):
      raise SmvUnsupported(
          f"both programs define procedure {proc.procname.name!r} with different "
          "bodies; inlining them into one model would let one definition win")
  return merged


def compose_with_inverse(prog_a: Program, prog_b: Program) -> Program:
  """Build `P; Q†` as a single Janus program.

  The interfaces must already agree; `main`'s initializers are dropped so that
  `init="any"` really leaves the store unconstrained (a declared initializer
  overrides the mode in `smv.py`).
  """
  iface_a, iface_b = _interface(prog_a), _interface(prog_b)
  if iface_a != iface_b:
    raise SmvUnsupported(
        "the two programs declare different main variables:\n"
        f"  P: {'; '.join(iface_a)}\n  Q: {'; '.join(iface_b)}")
  # The composed program carries `P`'s struct definitions, so a type name that
  # means something else in `Q` would have `Q†`'s field accesses resolved
  # against the wrong layout — silently, since the interface still matches on
  # the type *name*.
  defs_a = {sd.ident.name: format_struct_def(sd) for sd in (prog_a.struct_defs or [])}
  defs_b = {sd.ident.name: format_struct_def(sd) for sd in (prog_b.struct_defs or [])}
  for name in defs_a.keys() & defs_b.keys():
    if defs_a[name] != defs_b[name]:
      raise SmvUnsupported(
          f"both programs define struct {name!r} with different fields; "
          "the composition would resolve one program's fields against the "
          "other's layout")
  assert prog_a.main is not None and prog_b.main is not None
  body = list(prog_a.main.stmts) + invert_stmts(prog_b.main.stmts, global_mode=False)
  vdecls = [replace(v, init_expr=None) for v in prog_a.main.vdecls]
  main = replace(prog_a.main, vdecls=vdecls, stmts=body)
  return Program(main, _merged_procs(prog_a, prog_b), prog_a.struct_defs)


def _interface_smv_names(program: Program) -> list[str]:
  """The SMV base names `main`'s declarations turn into, in order.

  A struct does not survive as one variable: `smv.py` gives every field its own
  SMV name, `{var}_{field}` (`_declare_struct`), and an array — whether the
  declaration is an array of structs or the field itself is an array — becomes
  one native array hanging off that same name.  So the interface of a program
  declaring `point p` with fields `x`, `y` is `p_x`, `p_y`.

  Only the *names* are derived here.  Whether each one really exists is checked
  against the emitted model, so a name `smv.py` renamed is refused rather than
  silently dropped from the identity property.
  """
  if program.main is None:
    raise SmvUnsupported("the program has no main procedure")
  structs = {sd.ident.name: sd for sd in (program.struct_defs or [])}
  out: list[str] = []
  for vdecl in program.main.vdecls:
    if vdecl.typ.kind != "struct":
      out.append(vdecl.ident.name)
      continue
    sdef = structs.get(vdecl.typ.name)
    if sdef is None:
      raise SmvUnsupported(f"unknown struct type: {vdecl.typ.name}")
    for field_ in sdef.fields:
      out.append(f"{vdecl.ident.name}_{field_.ident.name}")
  return out


def _model_variables(model: str) -> tuple[dict[str, int | None], set[str]]:
  """Read the `VAR` block: name → array length, or None for a scalar."""
  found: dict[str, int | None] = {}
  for m in _SCALAR_RE.finditer(model):
    found[m.group("name")] = None
  for m in _ARRAY_RE.finditer(model):
    found[m.group("name")] = int(m.group("hi")) + 1
  return found, set(found)


def _identity_spec(model: str, names: list[str]) -> tuple[str, str, tuple[str, ...]]:
  """Return (declarations block, INVARSPEC line, compared names)."""
  final_match = _FINAL_RE.search(model)
  if final_match is None:
    raise SmvUnsupported(
        "could not find the 'normal termination' marker in the emitted model; "
        "smv.py's rendering changed and this checker must be updated with it")
  final = final_match.group("final")

  declared, all_names = _model_variables(model)
  if any(n.endswith(_FROZEN_SUFFIX) for n in all_names):
    raise SmvUnsupported(
        f"a model variable already ends in {_FROZEN_SUFFIX!r}; "
        "the frozen-copy names would collide")

  decls: list[str] = ["FROZENVAR"]
  ties: list[str] = []
  equalities: list[str] = []
  compared: list[str] = []
  for name in names:
    if name not in declared:
      raise SmvUnsupported(
          f"interface variable {name!r} does not appear verbatim in the model "
          "(smv.py renames names that collide with nuXmv keywords); "
          "equivalence checking does not track the renaming")
    frozen = name + _FROZEN_SUFFIX
    size = declared[name]
    if size is None:
      decls.append(f"  {frozen} : integer;")
      ties.append(f"{frozen} = {name}")
      equalities.append(f"{name} = {frozen}")
    else:
      decls.append(f"  {frozen} : array 0..{size - 1} of integer;")
      for i in range(size):
        ties.append(f"{frozen}[{i}] = {name}[{i}]")
        equalities.append(f"{name}[{i}] = {frozen}[{i}]")
    compared.append(name)

  if not equalities:
    raise SmvUnsupported(
        "the programs declare no interface variables, so the identity "
        "property would be vacuous")

  block = "\n".join(decls) + "\n\nINIT\n  " + " & ".join(ties) + ";\n"
  spec = f"INVARSPEC pc != {final} | ({' & '.join(equalities)})"
  return block, spec, tuple(compared)


def compile_equivalence_to_smv(prog_a: Program, prog_b: Program, **kw) -> EquivModel:
  """Emit an nuXmv model that is fully proved iff `P` and `Q` agree everywhere.

  Keyword arguments are passed to `smv.compile_to_smv`, except `init`, which is
  forced to `"any"`: an equivalence proof that only covered the zero store
  would be a proof about one input.
  """
  if kw.pop("init", "any") != "any":
    raise ValueError("equivalence is asked over every store; init must be 'any'")
  composed = compose_with_inverse(prog_a, prog_b)
  model = compile_to_smv(composed, init="any", **kw)

  block, spec, compared = _identity_spec(model, _interface_smv_names(prog_a))

  # The declarations have to precede the specs: nuXmv reads the file in order
  # and a FROZENVAR introduced after an INVARSPEC is a parse error.
  head, sep, tail = model.partition("INVARSPEC")
  if not sep:
    raise SmvUnsupported("the emitted model has no INVARSPEC to anchor against")
  out = head + block + "\n" + sep + tail
  if not out.endswith("\n"):
    out += "\n"
  return EquivModel(out + spec + "\n", spec, compared)


def _weakest(statuses: list[str]) -> str:
  for want in ("refuted", "unknown"):
    if want in statuses:
      return want
  return "proved" if statuses else "unknown"


def check_equivalence_smv(prog_a: Program, prog_b: Program, *, timeout: float = 60.0,
                          binary=None, **kw) -> EquivVerdict:
  """Decide `P ≡ Q` with nuXmv's IC3.  Raises if nuXmv is not installed."""
  built = compile_equivalence_to_smv(prog_a, prog_b, **kw)
  result = check(built.model, timeout=timeout, binary=binary)
  if result.malformed:
    return EquivVerdict(status="model-error", result=result)

  # nuXmv reprints a property with its own parenthesisation, so the emitted
  # text cannot be matched literally.  The frozen names occur in no other
  # property, which makes them a reliable discriminator.
  identity_v = [v for v in result.verdicts if _FROZEN_SUFFIX in v.prop]
  other_v = [v for v in result.verdicts if _FROZEN_SUFFIX not in v.prop]
  identity = _weakest([v.status for v in identity_v])
  totality = _weakest([v.status for v in other_v])

  if result.timed_out or not result.verdicts:
    status = "unknown"
  elif identity == "refuted":
    status = "different"
  elif identity == "proved":
    status = "equivalent" if totality == "proved" else "partial"
  else:
    status = "unknown"

  counterexample: dict[str, int] = {}
  if status == "different":
    for verdict in identity_v:
      if verdict.status == "refuted" and verdict.counterexample:
        counterexample = {k: v for k, v in verdict.counterexample.items()
                          if not k.endswith(_FROZEN_SUFFIX)}
        break
  return EquivVerdict(status=status, counterexample=counterexample,
                      identity=identity, totality=totality, result=result)
