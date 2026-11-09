"""Space complexity analysis (pebble game / memory profiling) for Jana programs.

In reversible computing, intermediate values cannot be discarded (Landauer's
principle).  The "pebble game" models this: each variable that holds a non-zero
value is a "pebble" on the computation graph.  The goal is to minimize the
maximum number of simultaneous pebbles.

This module provides a SpaceProfiler that wraps Runtime execution and records
per-step memory snapshots without altering program behavior.

It also measures the RC-03 "resource atlas" vector (steps, stack_peak,
call_depth_peak, final_live_bits, per-array puts/takes, erasures) by scanning
the live frames after every executed statement; storage is identified by
identity so reference-passed stacks/arrays are never double counted.  See
``tests/resource_atlas/README.md`` for the definitions.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any

from .ast import (
    AssignStmt,
    CallStmt,
    Expr,
    LocalStmt,
    Program,
    SourcePos,
    SwapStmt,
    UncallStmt,
)
from .runtime import ArraySliceProxy, Cell, Frame, Runtime


# ---------------------------------------------------------------------------
# Data classes
# ---------------------------------------------------------------------------

@dataclass
class SpaceSnapshot:
    """A single point-in-time observation of memory usage."""
    step: int
    line: int
    live_vars: int        # count of non-zero variables at this point
    live_bits: int        # total bit-width of non-zero values
    call_depth: int
    event: str            # "assign", "swap", "call", "uncall", "local", "delocal", etc.


@dataclass
class ArrayStats:
    """Per-array put/take census (RC-03 ``puts`` / ``takes``).

    A *put* is a cell transition 0 -> non-0, a *take* the reverse, both
    observed statement by statement.  Arrays are identified by the identity
    of their storage (so an array passed by reference is one array, however
    many frames hold it) and reported under the name they had in the frame
    where they were first seen.  A local array that is allocated several
    times (e.g. inside a loop) contributes several ``instances`` to the same
    name.
    """
    name: str
    size: int = 0               # total cells over all instances
    puts: int = 0
    takes: int = 0
    instances: int = 1
    end_nonzero: int = 0        # non-zero cells at the last observation
    live_at_end: bool = False   # still held by a live frame when main ended

    @property
    def written(self) -> bool:
        return self.puts > 0

    @property
    def ends_empty(self) -> bool:
        return self.end_nonzero == 0


@dataclass
class SpaceProfile:
    """Aggregate result of a profiling run.

    The first block of fields is the historical pebble profile; the second
    block is the RC-03 resource vector (steps, stack_peak, call_depth_peak,
    final_live_bits, puts/takes, erasures).  ``steps`` and ``call_depth_peak``
    are aliases of ``total_steps`` / ``call_depth_max``.
    """
    max_live_vars: int          # peak number of non-zero variables
    max_live_bits: int          # peak total bits of non-zero data
    total_steps: int            # total statement executions
    timeline: list[SpaceSnapshot] = field(default_factory=list)
    call_depth_max: int = 0     # maximum call stack depth
    local_var_max: int = 0      # peak local (ancilla) variables
    # --- RC-03 resource vector -------------------------------------------
    stack_peak: int = 0         # peak total depth of all Janus `stack`s (identity-deduplicated)
    total_calls: int = 0        # number of call + uncall events
    final_live_bits: int = 0    # bits of non-zero state when main ends
    arrays: dict[str, ArrayStats] = field(default_factory=dict)
    erasures: int = 0           # irreversible erasures: identically 0 in Janus

    @property
    def steps(self) -> int:
        return self.total_steps

    @property
    def call_depth_peak(self) -> int:
        return self.call_depth_max


# ---------------------------------------------------------------------------
# Bit-width measurement
# ---------------------------------------------------------------------------

def _value_bits(value: Any) -> int:
    """Return the information content (bit-width) of a non-zero value.

    - int: bit_length()
    - bool: 1 if True, 0 if False
    - list (array/stack): sum of element bits
    - dict (struct): sum of field bits
    """
    if isinstance(value, bool):
        return 1 if value else 0
    if isinstance(value, int):
        return value.bit_length() if value != 0 else 0
    if isinstance(value, list):
        return sum(_value_bits(item) for item in value)
    if isinstance(value, dict):
        return sum(_value_bits(v) for v in value.values())
    return 0


def _is_zero(value: Any) -> bool:
    """Check whether a value is semantically zero (cleared)."""
    if isinstance(value, bool):
        return not value
    if isinstance(value, int):
        return value == 0
    if isinstance(value, list):
        return all(_is_zero(item) for item in value)
    if isinstance(value, dict):
        return all(_is_zero(v) for v in value.values())
    return False


# ---------------------------------------------------------------------------
# Frame inspection
# ---------------------------------------------------------------------------

def _count_frame(frame: Frame) -> tuple[int, int]:
    """Count live (non-zero) variables and total bits in a frame."""
    live = 0
    bits = 0
    for cell in frame.vars.values():
        if not _is_zero(cell.value):
            live += 1
            bits += _value_bits(cell.value)
    return live, bits


def _count_all_frames(frames: list[Frame]) -> tuple[int, int]:
    """Aggregate live counts across all active frames."""
    total_live = 0
    total_bits = 0
    for frame in frames:
        live, bits = _count_frame(frame)
        total_live += live
        total_bits += bits
    return total_live, total_bits


def _is_zero_fast(value: Any) -> bool:
    """`_is_zero` with a fast path for plain ints (the common array element)."""
    if type(value) is int:
        return value == 0
    return _is_zero(value)


class _ArrayTrack:
    """Bookkeeping for one array *storage* (one Python list)."""
    __slots__ = ("name", "ref", "zero", "puts", "takes")

    def __init__(self, name: str, ref: list):
        self.name = name
        # Hold a reference so the list can never be freed and its id() reused
        # by a different array while we still key on it.
        self.ref = ref
        self.zero = [_is_zero_fast(x) for x in ref]
        self.puts = 0
        self.takes = 0

    def observe(self) -> None:
        zero = self.zero
        for i, x in enumerate(self.ref):
            z = _is_zero_fast(x)
            if z != zero[i]:
                if z:
                    self.takes += 1
                else:
                    self.puts += 1
                zero[i] = z


# ---------------------------------------------------------------------------
# Profiling Runtime subclass
# ---------------------------------------------------------------------------

class _ProfilingRuntime(Runtime):
    """Runtime subclass that records space snapshots after each statement."""

    def __init__(self, program: Program, **kwargs: Any):
        super().__init__(program, **kwargs)
        self._step_count: int = 0
        self._call_depth: int = 0
        self._local_var_count: int = 0
        self._frames: list[Frame] = []
        self._snapshots: list[SpaceSnapshot] = []
        self._peak_live_vars: int = 0
        self._peak_live_bits: int = 0
        self._peak_call_depth: int = 0
        self._peak_local_vars: int = 0
        # RC-03 resource vector.  `_live_frames` is a proper frame *stack*
        # (root frame + one frame per active call), unlike the historical
        # `_frames` list above, which keeps every frame ever executed in and
        # is retained unchanged so that max_live_vars / max_live_bits keep
        # their historical values.
        self._live_frames: list[Frame] = []
        self._stack_peak: int = 0
        self._total_calls: int = 0
        self._arrays: dict[int, _ArrayTrack] = {}
        self._array_names: dict[str, int] = {}
        self._final_live_bits: int = 0

    # -- hooks ---------------------------------------------------------------

    def run(self) -> str:
        if self.program.main is None:
            from .errors import JanaError
            raise JanaError(SourcePos("", 0, 0), "No main procedure has been defined")
        frame = Frame(vars={})
        self._root_frame = frame
        self._frames = [frame]
        self._live_frames = [frame]
        self.main_vdecls = list(self.program.main.vdecls)
        self._first_stmt_line = (
            self.program.main.stmts[0].pos.line
            if self.program.main.stmts
            else self.program.main.pos.line
        )
        self._init_vdecls(frame, self.program.main.vdecls)
        # Record initial snapshot
        self._record_snapshot(
            line=self.program.main.pos.line,
            event="init",
        )
        self._exec_block(frame, self.program.main.stmts)
        self._scan_resources()
        self._final_live_bits = self._live_bits(self._live_frames)
        store = self._format_store(frame)
        return "".join(self.stdout) + store + ("\n" if store else "")

    def _exec_stmt_impl(
        self,
        frame: Frame,
        stmt: Any,
        allow_break: bool,
        record_stmt: bool,
        record_nested: bool = False,
    ) -> None:
        # Track the current frame for measurement (the frame being executed in)
        if frame not in self._frames:
            self._frames.append(frame)
        super()._exec_stmt_impl(
            frame, stmt,
            allow_break=False,      # disable debugger in profiling mode
            record_stmt=record_stmt,
            record_nested=record_nested,
        )
        self._step_count += 1
        event = self._event_name(stmt)
        self._record_snapshot(line=stmt.pos.line, event=event)

    def _call_proc(
        self,
        caller: Frame,
        name: str,
        args: list[Expr],
        pos: SourcePos,
        record_stmt: bool = True,
        record_nested: bool = False,
    ) -> None:
        self._call_depth += 1
        self._total_calls += 1
        if self._call_depth > self._peak_call_depth:
            self._peak_call_depth = self._call_depth
        n_live = len(self._live_frames)
        try:
            super()._call_proc(
                caller, name, args, pos,
                record_stmt=record_stmt,
                record_nested=record_nested,
            )
        finally:
            self._call_depth -= 1
            del self._live_frames[n_live:]

    def _uncall_proc(
        self,
        caller: Frame,
        name: str,
        args: list[Expr],
        pos: SourcePos,
        record_stmt: bool = True,
        record_nested: bool = False,
    ) -> None:
        self._call_depth += 1
        self._total_calls += 1
        if self._call_depth > self._peak_call_depth:
            self._peak_call_depth = self._call_depth
        n_live = len(self._live_frames)
        try:
            super()._uncall_proc(
                caller, name, args, pos,
                record_stmt=record_stmt,
                record_nested=record_nested,
            )
        finally:
            self._call_depth -= 1
            del self._live_frames[n_live:]

    def _exec_local(
        self,
        frame: Frame,
        stmt: LocalStmt,
        record_stmt: bool = True,
        record_nested: bool = False,
    ) -> None:
        self._local_var_count += 1
        if self._local_var_count > self._peak_local_vars:
            self._peak_local_vars = self._local_var_count
        try:
            super()._exec_local(frame, stmt, record_stmt=record_stmt, record_nested=record_nested)
        finally:
            self._local_var_count -= 1

    def _bind_args(self, caller: Frame, name: str, args: list[Expr], pos: SourcePos):
        proc, frame, value_checks = super()._bind_args(caller, name, args, pos)
        # The callee frame becomes live here; `_call_proc`/`_uncall_proc`
        # truncate `_live_frames` back on return (also on error).
        self._live_frames.append(frame)
        return proc, frame, value_checks

    # -- RC-03 resource scan -------------------------------------------------

    def _scan_resources(self) -> None:
        """Scan the live frames once: stack depth (peak) and array put/take.

        Cells are identified by the identity of their storage (`id()` of the
        underlying list), so a stack or array passed by reference is counted
        once no matter how many frames hold it (rc03.tex:120).
        """
        seen_stacks: set[int] = set()
        seen_arrays: set[int] = set()
        depth = 0
        arrays = self._arrays
        for frame in self._live_frames:
            for name, cell in frame.vars.items():
                if isinstance(cell, ArraySliceProxy):
                    # A sub-array view: its storage is the owner's array,
                    # which is tracked through the owner's frame.
                    continue
                value = cell.value
                if not isinstance(value, list):
                    continue
                key = id(value)
                if cell.kind == "stack":
                    if key not in seen_stacks:
                        seen_stacks.add(key)
                        depth += len(value)
                elif cell.shape is not None:
                    if key in seen_arrays:
                        continue
                    seen_arrays.add(key)
                    track = arrays.get(key)
                    if track is None:
                        arrays[key] = _ArrayTrack(name, value)
                    else:
                        track.observe()
        if depth > self._stack_peak:
            self._stack_peak = depth

    @staticmethod
    def _live_bits(frames: list[Frame]) -> int:
        """Bits of non-zero state held by `frames`, mutable storage deduplicated."""
        seen: set[int] = set()
        bits = 0
        for frame in frames:
            for cell in frame.vars.values():
                value = cell.value
                if isinstance(value, (list, dict)):
                    key = id(value)
                    if key in seen:
                        continue
                    seen.add(key)
                bits += _value_bits(value)
        return bits

    def _array_stats(self) -> dict[str, ArrayStats]:
        live_ids: set[int] = set()
        for frame in self._live_frames:
            for cell in frame.vars.values():
                value = cell.value
                if isinstance(value, list) and cell.shape is not None:
                    live_ids.add(id(value))
        stats: dict[str, ArrayStats] = {}
        for key, track in self._arrays.items():
            # `zero` is current as of the last scan (arrays are only mutated
            # by statements, and every statement is followed by a scan).
            end_nonzero = sum(1 for z in track.zero if not z)
            st = stats.get(track.name)
            if st is None:
                stats[track.name] = ArrayStats(
                    name=track.name, size=len(track.ref), puts=track.puts,
                    takes=track.takes, instances=1, end_nonzero=end_nonzero,
                    live_at_end=key in live_ids,
                )
            else:
                st.size += len(track.ref)
                st.puts += track.puts
                st.takes += track.takes
                st.instances += 1
                st.end_nonzero += end_nonzero
                st.live_at_end = st.live_at_end or key in live_ids
        return stats

    # -- internal helpers ----------------------------------------------------

    def _record_snapshot(self, line: int, event: str) -> None:
        self._scan_resources()
        live_vars, live_bits = _count_all_frames(self._frames)
        if live_vars > self._peak_live_vars:
            self._peak_live_vars = live_vars
        if live_bits > self._peak_live_bits:
            self._peak_live_bits = live_bits
        self._snapshots.append(SpaceSnapshot(
            step=self._step_count,
            line=line,
            live_vars=live_vars,
            live_bits=live_bits,
            call_depth=self._call_depth,
            event=event,
        ))

    @staticmethod
    def _event_name(stmt: Any) -> str:
        if isinstance(stmt, AssignStmt):
            return "assign"
        if isinstance(stmt, SwapStmt):
            return "swap"
        if isinstance(stmt, CallStmt):
            return "call"
        if isinstance(stmt, UncallStmt):
            return "uncall"
        if isinstance(stmt, LocalStmt):
            return "local"
        return type(stmt).__name__.lower().replace("stmt", "")

    def build_profile(self) -> SpaceProfile:
        return SpaceProfile(
            max_live_vars=self._peak_live_vars,
            max_live_bits=self._peak_live_bits,
            total_steps=self._step_count,
            timeline=list(self._snapshots),
            call_depth_max=self._peak_call_depth,
            local_var_max=self._peak_local_vars,
            stack_peak=self._stack_peak,
            total_calls=self._total_calls,
            final_live_bits=self._final_live_bits,
            arrays=self._array_stats(),
            erasures=0,
        )


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

def profile_space(program: Program, **kwargs: Any) -> SpaceProfile:
    """Run a program and collect space usage statistics.

    Accepts the same keyword arguments as ``Runtime.__init__`` (except
    ``debug`` which is forced off).

    Returns a ``SpaceProfile`` with aggregate peaks and a full timeline.
    """
    kwargs.pop("debug", None)
    kwargs.pop("debug_on_error", None)
    rt = _ProfilingRuntime(program, **kwargs)
    rt.run()
    return rt.build_profile()


def format_profile(profile: SpaceProfile) -> str:
    """Return a human-readable summary of space usage."""
    lines: list[str] = [
        "=== Space Profile ===",
        f"Total steps:         {profile.total_steps}",
        f"Peak live variables: {profile.max_live_vars}",
        f"Peak live bits:      {profile.max_live_bits}",
        f"Max call depth:      {profile.call_depth_max}",
        f"Peak local vars:     {profile.local_var_max}",
        "--- RC-03 resource vector ---",
        f"Stack peak:          {profile.stack_peak}",
        f"Total calls:         {profile.total_calls}",
        f"Final live bits:     {profile.final_live_bits}",
        f"Erasures:            {profile.erasures}",
    ]
    if profile.arrays:
        lines.append("")
        lines.append("Arrays (name | size | puts | takes | end_nonzero):")
        for st in profile.arrays.values():
            lines.append(
                f"  {st.name:<12s} | {st.size:>5d} | {st.puts:>5d} | "
                f"{st.takes:>5d} | {st.end_nonzero:>5d}"
            )
    if profile.timeline:
        lines.append("")
        lines.append("Timeline (step | line | live_vars | live_bits | depth | event):")
        for snap in profile.timeline:
            lines.append(
                f"  {snap.step:>5d} | {snap.line:>4d} | "
                f"{snap.live_vars:>9d} | {snap.live_bits:>9d} | "
                f"{snap.call_depth:>5d} | {snap.event}"
            )
    return "\n".join(lines)


def profile_to_dict(profile: SpaceProfile, include_timeline: bool = False) -> dict[str, Any]:
    """Return a JSON-serialisable dict of the profile (RC-03 resource vector
    plus the historical pebble fields).  The timeline is omitted unless asked
    for, since it has one entry per executed statement."""
    out: dict[str, Any] = {
        "steps": profile.total_steps,
        "stack_peak": profile.stack_peak,
        "call_depth_peak": profile.call_depth_max,
        "total_calls": profile.total_calls,
        "final_live_bits": profile.final_live_bits,
        "erasures": profile.erasures,
        "arrays": {
            name: {
                "size": st.size,
                "puts": st.puts,
                "takes": st.takes,
                "instances": st.instances,
                "end_nonzero": st.end_nonzero,
                "live_at_end": st.live_at_end,
            }
            for name, st in profile.arrays.items()
        },
        "max_live_vars": profile.max_live_vars,
        "max_live_bits": profile.max_live_bits,
        "local_var_max": profile.local_var_max,
    }
    if include_timeline:
        out["timeline"] = [
            {"step": s.step, "line": s.line, "live_vars": s.live_vars,
             "live_bits": s.live_bits, "call_depth": s.call_depth, "event": s.event}
            for s in profile.timeline
        ]
    return out


def compare_profiles(a: SpaceProfile, b: SpaceProfile) -> str:
    """Compare two profiles side-by-side (e.g., forward vs Bennett-embedded)."""

    def _delta(label: str, va: int, vb: int) -> str:
        diff = vb - va
        sign = "+" if diff > 0 else ""
        return f"  {label:<22s}  {va:>8d}  {vb:>8d}  {sign}{diff}"

    lines: list[str] = [
        "=== Profile Comparison ===",
        f"  {'Metric':<22s}  {'A':>8s}  {'B':>8s}  {'Delta':>8s}",
        "  " + "-" * 54,
        _delta("Total steps", a.total_steps, b.total_steps),
        _delta("Peak live variables", a.max_live_vars, b.max_live_vars),
        _delta("Peak live bits", a.max_live_bits, b.max_live_bits),
        _delta("Max call depth", a.call_depth_max, b.call_depth_max),
        _delta("Peak local vars", a.local_var_max, b.local_var_max),
        _delta("Stack peak", a.stack_peak, b.stack_peak),
        _delta("Total calls", a.total_calls, b.total_calls),
        _delta("Final live bits", a.final_live_bits, b.final_live_bits),
    ]
    return "\n".join(lines)
