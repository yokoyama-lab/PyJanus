"""Space complexity analysis (pebble game / memory profiling) for Jana programs.

In reversible computing, intermediate values cannot be discarded (Landauer's
principle).  The "pebble game" models this: each variable that holds a non-zero
value is a "pebble" on the computation graph.  The goal is to minimize the
maximum number of simultaneous pebbles.

This module provides a SpaceProfiler that wraps Runtime execution and records
per-step memory snapshots without altering program behavior.
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
from .runtime import Cell, Frame, Runtime


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
class SpaceProfile:
    """Aggregate result of a profiling run."""
    max_live_vars: int          # peak number of non-zero variables
    max_live_bits: int          # peak total bits of non-zero data
    total_steps: int            # total statement executions
    timeline: list[SpaceSnapshot] = field(default_factory=list)
    call_depth_max: int = 0     # maximum call stack depth
    local_var_max: int = 0      # peak local (ancilla) variables


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

    # -- hooks ---------------------------------------------------------------

    def run(self) -> str:
        if self.program.main is None:
            from .errors import JanaError
            raise JanaError(SourcePos("", 0, 0), "No main procedure has been defined")
        frame = Frame(vars={})
        self._root_frame = frame
        self._frames = [frame]
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
        if self._call_depth > self._peak_call_depth:
            self._peak_call_depth = self._call_depth
        try:
            super()._call_proc(
                caller, name, args, pos,
                record_stmt=record_stmt,
                record_nested=record_nested,
            )
        finally:
            self._call_depth -= 1

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
        if self._call_depth > self._peak_call_depth:
            self._peak_call_depth = self._call_depth
        try:
            super()._uncall_proc(
                caller, name, args, pos,
                record_stmt=record_stmt,
                record_nested=record_nested,
            )
        finally:
            self._call_depth -= 1

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

    # -- internal helpers ----------------------------------------------------

    def _record_snapshot(self, line: int, event: str) -> None:
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
    ]
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
    ]
    return "\n".join(lines)
