"""Janus 1982 extended parser (`janus1982ext`).

This dialect is currently grammar-identical to `jana2014basic` (the file used
to be a byte-for-byte copy of `parser_jana2014basic.py`), so it simply
re-exports that parser. If the extended-1982 grammar ever diverges, turn this
into a subclass overriding the differing productions (see
`parser_jana2014_in_out.py` for the pattern).
"""
from __future__ import annotations

from .parser_jana2014basic import KEYWORDS
from .parser_jana2014basic import Parser
from .parser_jana2014basic import parse_program
from .parser_jana2014basic import tokenize

__all__ = ["KEYWORDS", "Parser", "parse_program", "tokenize"]
