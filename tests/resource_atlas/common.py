"""Shared helpers for the resource atlas scripts: locating the corpus,
loading a program in the right dialect, and profiling it with a timeout."""
from __future__ import annotations

import io
import signal
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from jana_py.ast import Program  # noqa: E402
from jana_py.cli import parse_for_std  # noqa: E402
from jana_py.costcheck import CostPrediction, analyze  # noqa: E402
from jana_py.pebble import SpaceProfile, profile_space  # noqa: E402
from jana_py.preprocess import preprocess_text  # noqa: E402
from jana_py.validate import validate_program  # noqa: E402

ATLAS_DIR = ROOT / "tests" / "resource_atlas"
GENERATED_DIR = ATLAS_DIR / "generated"
DATA_DIR = ATLAS_DIR / "data"

# The 101-program corpus: (directory, --std used by that directory's tests).
CORPUS_DIRS: list[tuple[Path, str]] = [
    (ROOT / "tests" / "jana2014" / "fixtures" / "examples", "jana2014"),
    (ROOT / "tests" / "jana2014_in_out" / "fixtures" / "examples", "jana2014_in_out"),
    (ROOT / "tests" / "janus2026" / "fixtures" / "examples", "janus2026"),
    (ROOT / "tests" / "jana2014basic" / "fixtures" / "examples", "jana2014basic"),
]

DEFAULT_TIMEOUT = 120  # seconds per program


def corpus_files() -> list[tuple[Path, str]]:
    """All corpus programs as (path, std), sorted per directory."""
    out: list[tuple[Path, str]] = []
    for directory, std in CORPUS_DIRS:
        for path in sorted(directory.glob("*.ja")):
            out.append((path, std))
    return out


def rel(path: Path) -> str:
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        return str(path)


def load_program(path: Path, std: str, text: str | None = None) -> Program:
    """preprocess -> parse (dialect `std`) -> validate, like the CLI does."""
    source = path.read_text() if text is None else text
    pre = preprocess_text(str(path), source, include_dirs=[], std=std)
    program = parse_for_std(std, str(path), pre.text, pre.line_origins)
    validate_program(program)
    return program


class _Timeout(Exception):
    pass


def _alarm(signum, frame):  # pragma: no cover - signal handler
    raise _Timeout()


@dataclass
class Measurement:
    path: Path
    std: str
    profile: SpaceProfile | None
    prediction: CostPrediction | None
    error: str | None

    @property
    def ok(self) -> bool:
        return self.profile is not None


def measure(path: Path, std: str, text: str | None = None,
            timeout: int = DEFAULT_TIMEOUT) -> Measurement:
    """Profile one program (and run the static analyzer on it).

    Never raises: parse/validation/runtime failures and timeouts are
    reported in `error`, so a failing program still gets a row.
    """
    prediction: CostPrediction | None = None
    try:
        program = load_program(path, std, text)
    except Exception as exc:  # noqa: BLE001 - we record every failure kind
        return Measurement(path, std, None, None, f"{type(exc).__name__}: {_one_line(exc)}")
    try:
        prediction = analyze(program)
    except Exception as exc:  # noqa: BLE001
        return Measurement(path, std, None, None, f"costcheck {type(exc).__name__}: {_one_line(exc)}")
    old_stdin = sys.stdin
    old_limit = sys.getrecursionlimit()
    sys.stdin = io.StringIO("")
    sys.setrecursionlimit(max(old_limit, 20000))
    old_handler = signal.signal(signal.SIGALRM, _alarm)
    signal.alarm(timeout)
    try:
        profile = profile_space(program, std=std)
        return Measurement(path, std, profile, prediction, None)
    except _Timeout:
        return Measurement(path, std, None, prediction, f"timeout after {timeout}s")
    except RecursionError:
        return Measurement(path, std, None, prediction, "RecursionError")
    except Exception as exc:  # noqa: BLE001
        return Measurement(path, std, None, prediction, f"{type(exc).__name__}: {_one_line(exc)}")
    finally:
        signal.alarm(0)
        signal.signal(signal.SIGALRM, old_handler)
        sys.stdin = old_stdin
        sys.setrecursionlimit(old_limit)


def _one_line(exc: BaseException) -> str:
    msg = getattr(exc, "message", None) or str(exc)
    return " ".join(str(msg).split())[:200]


def resource_row(profile: SpaceProfile) -> dict[str, Any]:
    """The RC-03 resource vector of a profile as flat CSV-ready values."""
    return {
        "steps": profile.total_steps,
        "stack_peak": profile.stack_peak,
        "call_depth_peak": profile.call_depth_max,
        "total_calls": profile.total_calls,
        "final_live_bits": profile.final_live_bits,
        "erasures": profile.erasures,
    }
