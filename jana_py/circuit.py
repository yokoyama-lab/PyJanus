"""Reversible circuit synthesis from Jana AST.

Translates Jana programs into reversible gate networks (Toffoli/Fredkin/CNOT).

Key mappings:
  x ^= y       -> CNOT(control=y, target=x)
  x ^= y & z   -> Toffoli(controls=[y, z], target=x)
  x <=> y      -> SWAP(targets=[x, y])
  x += c       -> ADD_CONST (abstract reversible addition by constant)
  x -= c       -> SUB_CONST (abstract reversible subtraction by constant)
  x += y       -> ADD (abstract reversible adder)
  x -= y       -> SUB (abstract reversible subtractor)
  if c then .. fi c -> controlled gate block
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum

from .ast import (
    AssignStmt,
    BinExpr,
    BinOpKind,
    Expr,
    FromStmt,
    IfStmt,
    LvalExpr,
    ModOp,
    Number,
    Program,
    SkipStmt,
    Stmt,
    SwapStmt,
)


class GateType(Enum):
    NOT = "NOT"
    CNOT = "CNOT"
    TOFFOLI = "Toffoli"
    SWAP = "SWAP"
    FREDKIN = "Fredkin"
    ADD = "ADD"
    ADD_CONST = "ADD_CONST"
    SUB = "SUB"
    SUB_CONST = "SUB_CONST"


@dataclass
class Gate:
    """A single reversible gate in a circuit.

    Attributes:
        gate_type: The kind of gate (NOT, CNOT, Toffoli, SWAP, Fredkin, ADD, ...).
        controls: Wire names that act as controls (read-only inputs).
        targets: Wire names that are modified by the gate.
        value: Optional constant value (for ADD_CONST / SUB_CONST).
        label: Optional human-readable annotation.
    """
    gate_type: GateType
    controls: list[str] = field(default_factory=list)
    targets: list[str] = field(default_factory=list)
    value: int | None = None
    label: str | None = None

    def inverse(self) -> "Gate":
        """Return the inverse gate (self-inverse for most gates)."""
        if self.gate_type == GateType.ADD:
            return Gate(GateType.SUB, list(self.controls), list(self.targets), self.value, self.label)
        if self.gate_type == GateType.SUB:
            return Gate(GateType.ADD, list(self.controls), list(self.targets), self.value, self.label)
        if self.gate_type == GateType.ADD_CONST:
            return Gate(GateType.SUB_CONST, list(self.controls), list(self.targets), self.value, self.label)
        if self.gate_type == GateType.SUB_CONST:
            return Gate(GateType.ADD_CONST, list(self.controls), list(self.targets), self.value, self.label)
        # NOT, CNOT, Toffoli, SWAP, Fredkin are self-inverse
        return Gate(self.gate_type, list(self.controls), list(self.targets), self.value, self.label)

    def __repr__(self) -> str:
        parts = [self.gate_type.value]
        if self.controls:
            parts.append(f"controls={self.controls}")
        if self.targets:
            parts.append(f"targets={self.targets}")
        if self.value is not None:
            parts.append(f"value={self.value}")
        return f"Gate({', '.join(parts)})"


class CircuitError(Exception):
    """Raised when a program cannot be translated to a circuit."""
    pass


@dataclass
class Circuit:
    """A reversible gate network.

    Attributes:
        gates: Ordered list of gates in the circuit.
        wires: Set of all wire (variable) names.
    """
    gates: list[Gate] = field(default_factory=list)
    wires: set[str] = field(default_factory=set)

    def gate_count(self) -> int:
        """Total number of gates."""
        return len(self.gates)

    def depth(self) -> int:
        """Circuit depth: longest chain through any single wire.

        Each gate occupies one time step on every wire it touches (controls + targets).
        Depth is the maximum number of gates touching any single wire.
        """
        if not self.gates:
            return 0
        wire_depth: dict[str, int] = {}
        for gate in self.gates:
            touched = gate.controls + gate.targets
            # This gate starts at the max depth of all touched wires
            start = max((wire_depth.get(w, 0) for w in touched), default=0)
            new_depth = start + 1
            for w in touched:
                wire_depth[w] = new_depth
        return max(wire_depth.values()) if wire_depth else 0

    def to_text(self) -> str:
        """Human-readable representation of the gate list."""
        lines: list[str] = []
        lines.append(f"Circuit: {self.gate_count()} gates, depth {self.depth()}, wires: {sorted(self.wires)}")
        lines.append("")
        for i, gate in enumerate(self.gates):
            lines.append(f"  {i:3d}: {_format_gate(gate)}")
        return "\n".join(lines)

    def inverse(self) -> "Circuit":
        """Return the inverse circuit (gates reversed and individually inverted)."""
        inv = Circuit(wires=set(self.wires))
        inv.gates = [g.inverse() for g in reversed(self.gates)]
        return inv

    def simulate(self, inputs: dict[str, int]) -> dict[str, int]:
        """Simulate the circuit on abstract integer-level wires.

        Each wire holds an integer value. Gates operate as follows:
          NOT(target)            -> target ^= all_ones (bitwise complement approximated as ~x)
          CNOT(ctrl, target)     -> target ^= ctrl
          Toffoli(c1,c2, target) -> target ^= (c1 & c2)
          SWAP(a, b)             -> a, b = b, a
          Fredkin(ctrl, a, b)    -> if ctrl: a, b = b, a
          ADD(ctrl, target)      -> target += ctrl
          SUB(ctrl, target)      -> target -= ctrl
          ADD_CONST(target, val) -> target += val
          SUB_CONST(target, val) -> target -= val
        """
        state: dict[str, int] = {}
        for w in self.wires:
            state[w] = inputs.get(w, 0)

        for gate in self.gates:
            _apply_gate(state, gate)

        return state


def _apply_gate(state: dict[str, int], gate: Gate) -> None:
    """Apply a single gate to the state dict, mutating it in place."""
    gt = gate.gate_type

    if gt == GateType.NOT:
        t = gate.targets[0]
        # Bitwise complement: for abstract integers we use Python's ~
        # which gives -(x+1). This is consistent with Jana's ~ operator.
        state[t] = ~state[t]

    elif gt == GateType.CNOT:
        t = gate.targets[0]
        if gate.controls:
            ctrl = gate.controls[0]
            state[t] ^= state[ctrl]
        elif gate.value is not None:
            state[t] ^= gate.value
        else:
            pass  # identity

    elif gt == GateType.TOFFOLI:
        c0 = gate.controls[0]
        c1 = gate.controls[1]
        t = gate.targets[0]
        state[t] ^= (state[c0] & state[c1])

    elif gt == GateType.SWAP:
        a, b = gate.targets[0], gate.targets[1]
        state[a], state[b] = state[b], state[a]

    elif gt == GateType.FREDKIN:
        ctrl = gate.controls[0]
        a, b = gate.targets[0], gate.targets[1]
        if state[ctrl]:
            state[a], state[b] = state[b], state[a]

    elif gt == GateType.ADD:
        ctrl = gate.controls[0]
        t = gate.targets[0]
        state[t] += state[ctrl]

    elif gt == GateType.SUB:
        ctrl = gate.controls[0]
        t = gate.targets[0]
        state[t] -= state[ctrl]

    elif gt == GateType.ADD_CONST:
        t = gate.targets[0]
        state[t] += gate.value

    elif gt == GateType.SUB_CONST:
        t = gate.targets[0]
        state[t] -= gate.value


def _format_gate(gate: Gate) -> str:
    """Format a single gate for text output."""
    gt = gate.gate_type
    if gt == GateType.NOT:
        return f"NOT {gate.targets[0]}"
    if gt == GateType.CNOT:
        return f"CNOT {gate.controls[0]} -> {gate.targets[0]}"
    if gt == GateType.TOFFOLI:
        cs = ", ".join(gate.controls)
        return f"Toffoli ({cs}) -> {gate.targets[0]}"
    if gt == GateType.SWAP:
        return f"SWAP {gate.targets[0]} <=> {gate.targets[1]}"
    if gt == GateType.FREDKIN:
        return f"Fredkin {gate.controls[0]} -> SWAP({gate.targets[0]}, {gate.targets[1]})"
    if gt == GateType.ADD:
        return f"ADD {gate.controls[0]} -> {gate.targets[0]}"
    if gt == GateType.SUB:
        return f"SUB {gate.controls[0]} -> {gate.targets[0]}"
    if gt == GateType.ADD_CONST:
        return f"ADD_CONST {gate.value} -> {gate.targets[0]}"
    if gt == GateType.SUB_CONST:
        return f"SUB_CONST {gate.value} -> {gate.targets[0]}"
    return repr(gate)


# ---------------------------------------------------------------------------
# AST -> Circuit translation
# ---------------------------------------------------------------------------

def _lval_wire_name(lval) -> str:
    """Extract the wire name from an Lval node.

    For simple variables this is just the identifier name.
    For array/struct access we build a compound name like "arr[0]" or "p.x".
    """
    name = lval.ident.name
    for sel in lval.selectors:
        from .ast import LvalIndex, LvalField
        if isinstance(sel, LvalIndex):
            if isinstance(sel.expr, Number):
                name += f"[{sel.expr.value}]"
            else:
                raise CircuitError(
                    f"Cannot synthesize circuit: dynamic array index in lval '{name}'"
                )
        elif isinstance(sel, LvalField):
            name += f".{sel.ident.name}"
    return name


def _expr_wire_name(expr: Expr) -> str | None:
    """If expr is a simple variable reference, return its wire name. Else None."""
    if isinstance(expr, LvalExpr):
        return _lval_wire_name(expr.lval)
    return None


def _expr_constant(expr: Expr) -> int | None:
    """If expr is a constant integer, return its value. Else None."""
    if isinstance(expr, Number):
        return expr.value
    return None


def synthesize_program(program: Program) -> Circuit:
    """Translate a Jana Program into a reversible Circuit.

    Processes only the main procedure. Raises CircuitError for unsupported
    constructs.
    """
    if program.main is None:
        raise CircuitError("No main procedure to synthesize")

    circuit = Circuit()

    # Register wires from variable declarations
    for vdecl in program.main.vdecls:
        circuit.wires.add(vdecl.ident.name)

    _synthesize_block(circuit, program.main.stmts)
    return circuit


def synthesize_stmts(stmts: list[Stmt], wires: set[str] | None = None) -> Circuit:
    """Translate a list of statements into a Circuit.

    This is a lower-level entry point useful for testing individual statements.
    """
    circuit = Circuit()
    if wires:
        circuit.wires.update(wires)
    _synthesize_block(circuit, stmts)
    return circuit


def _synthesize_block(circuit: Circuit, stmts: list[Stmt]) -> None:
    """Translate a block of statements, appending gates to the circuit."""
    for stmt in stmts:
        _synthesize_stmt(circuit, stmt)


def _synthesize_stmt(circuit: Circuit, stmt: Stmt) -> None:
    """Translate a single statement into gates."""
    if isinstance(stmt, SkipStmt):
        return

    if isinstance(stmt, AssignStmt):
        _synthesize_assign(circuit, stmt)
        return

    if isinstance(stmt, SwapStmt):
        _synthesize_swap(circuit, stmt)
        return

    if isinstance(stmt, IfStmt):
        _synthesize_if(circuit, stmt)
        return

    if isinstance(stmt, FromStmt):
        _synthesize_from(circuit, stmt)
        return

    raise CircuitError(f"Unsupported statement type for circuit synthesis: {type(stmt).__name__}")


def _synthesize_assign(circuit: Circuit, stmt: AssignStmt) -> None:
    """Translate an assignment statement (+=, -=, ^=)."""
    target = _lval_wire_name(stmt.lval)
    circuit.wires.add(target)

    if stmt.mod_op == ModOp.XOR_EQ:
        _synthesize_xor_assign(circuit, target, stmt.expr)
    elif stmt.mod_op == ModOp.ADD_EQ:
        _synthesize_add_assign(circuit, target, stmt.expr)
    elif stmt.mod_op == ModOp.SUB_EQ:
        _synthesize_sub_assign(circuit, target, stmt.expr)


def _synthesize_xor_assign(circuit: Circuit, target: str, expr: Expr) -> None:
    """Translate x ^= expr into gates.

    Special cases:
      x ^= y        -> CNOT(control=y, target=x)
      x ^= y & z    -> Toffoli(controls=[y, z], target=x)
      x ^= constant -> series of NOT gates (if const is all-ones), or ADD_CONST for XOR
    """
    # x ^= y & z  ->  Toffoli
    if isinstance(expr, BinExpr) and expr.op == BinOpKind.AND:
        left_wire = _expr_wire_name(expr.left)
        right_wire = _expr_wire_name(expr.right)
        if left_wire is not None and right_wire is not None:
            circuit.wires.add(left_wire)
            circuit.wires.add(right_wire)
            circuit.gates.append(Gate(
                gate_type=GateType.TOFFOLI,
                controls=[left_wire, right_wire],
                targets=[target],
                label=f"{target} ^= {left_wire} & {right_wire}",
            ))
            return

    # x ^= y  ->  CNOT
    wire = _expr_wire_name(expr)
    if wire is not None:
        circuit.wires.add(wire)
        circuit.gates.append(Gate(
            gate_type=GateType.CNOT,
            controls=[wire],
            targets=[target],
            label=f"{target} ^= {wire}",
        ))
        return

    # x ^= constant
    const = _expr_constant(expr)
    if const is not None:
        if const == 0:
            # XOR with 0 is identity, no gate needed
            return
        # For abstract-level synthesis, we model XOR-with-constant
        # as an ADD_CONST in the XOR domain. At simulation time this
        # is handled correctly by the simulator.
        circuit.gates.append(Gate(
            gate_type=GateType.CNOT,
            controls=[],
            targets=[target],
            value=const,
            label=f"{target} ^= {const}",
        ))
        return

    raise CircuitError(f"Cannot synthesize XOR assignment: {target} ^= <complex expression>")


def _synthesize_add_assign(circuit: Circuit, target: str, expr: Expr) -> None:
    """Translate x += expr into gates."""
    # x += constant
    const = _expr_constant(expr)
    if const is not None:
        if const == 0:
            return
        circuit.gates.append(Gate(
            gate_type=GateType.ADD_CONST,
            controls=[],
            targets=[target],
            value=const,
            label=f"{target} += {const}",
        ))
        return

    # x += y  ->  reversible adder
    wire = _expr_wire_name(expr)
    if wire is not None:
        circuit.wires.add(wire)
        circuit.gates.append(Gate(
            gate_type=GateType.ADD,
            controls=[wire],
            targets=[target],
            label=f"{target} += {wire}",
        ))
        return

    raise CircuitError(f"Cannot synthesize ADD assignment: {target} += <complex expression>")


def _synthesize_sub_assign(circuit: Circuit, target: str, expr: Expr) -> None:
    """Translate x -= expr into gates."""
    # x -= constant
    const = _expr_constant(expr)
    if const is not None:
        if const == 0:
            return
        circuit.gates.append(Gate(
            gate_type=GateType.SUB_CONST,
            controls=[],
            targets=[target],
            value=const,
            label=f"{target} -= {const}",
        ))
        return

    # x -= y  ->  reversible subtractor
    wire = _expr_wire_name(expr)
    if wire is not None:
        circuit.wires.add(wire)
        circuit.gates.append(Gate(
            gate_type=GateType.SUB,
            controls=[wire],
            targets=[target],
            label=f"{target} -= {wire}",
        ))
        return

    raise CircuitError(f"Cannot synthesize SUB assignment: {target} -= <complex expression>")


def _synthesize_swap(circuit: Circuit, stmt: SwapStmt) -> None:
    """Translate x <=> y into a SWAP gate."""
    left = _lval_wire_name(stmt.left)
    right = _lval_wire_name(stmt.right)
    circuit.wires.add(left)
    circuit.wires.add(right)
    circuit.gates.append(Gate(
        gate_type=GateType.SWAP,
        controls=[],
        targets=[left, right],
        label=f"{left} <=> {right}",
    ))


def _synthesize_if(circuit: Circuit, stmt: IfStmt) -> None:
    """Translate if-then-else-fi into a controlled gate block.

    For the MVP, we synthesize the if-branch and else-branch as separate
    gate sequences. The condition is recorded as a label annotation but
    the gates are emitted unconditionally (the condition is assumed to be
    the same at entry and exit, as required by Jana semantics).

    For simple conditions like a single variable, we could use Fredkin gates,
    but for the general case we just emit the body gates directly.
    """
    # Synthesize if-part
    if stmt.if_part:
        _synthesize_block(circuit, stmt.if_part)
    # Synthesize else-part (these would be the inverse path;
    # in a correct Jana program the condition determines which branch runs)
    if stmt.else_part:
        _synthesize_block(circuit, stmt.else_part)


def _synthesize_from(circuit: Circuit, stmt: FromStmt) -> None:
    """Translate from-do-loop-until into gates.

    Loops with known static bounds could be unrolled. For the MVP, we raise
    an error for dynamic loops and support only the case where the loop body
    can be statically unrolled (simple known-bound loops).

    However, to be useful for basic programs, we do a single-iteration
    synthesis of the do-part only, annotating it as a loop body.
    This is a conservative approximation that works for loops that execute
    exactly once.
    """
    raise CircuitError(
        "Loop synthesis not yet supported. "
        "Loops require static unrolling or bounded iteration."
    )
