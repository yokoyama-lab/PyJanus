"""Backwards-compatible alias for the original parser module.

Historically the unified parser lived in ``jana_py.parser``; commit 01160f8
renamed it to ``jana_py.parser_jana2014``. The test suite and external callers
still import ``parse_program`` from here, written against that parser's
``procedure``-style syntax, so this module re-exports it.
"""

from __future__ import annotations

from .parser_jana2014 import parse_program

__all__ = ["parse_program"]
