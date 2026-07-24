"""Small SMT-LIB command scanner used for declaration discovery.

Z3 remains the actual parser.  This module only recovers command-level metadata
that Z3Py's Fixedpoint API does not expose directly (notably relation names).
"""

from __future__ import annotations

from collections.abc import Iterator
from dataclasses import dataclass


class SExprError(ValueError):
    """Raised for malformed command-level SMT-LIB input."""


@dataclass(frozen=True)
class Token:
    text: str
    offset: int


def tokenize_smt2(text: str) -> Iterator[Token]:
    """Yield SMT-LIB tokens while honoring comments, strings, and quoted names."""

    i = 0
    n = len(text)
    while i < n:
        ch = text[i]
        if ch.isspace():
            i += 1
            continue
        if ch == ";":
            newline = text.find("\n", i + 1)
            i = n if newline < 0 else newline + 1
            continue
        if ch in "()":
            yield Token(ch, i)
            i += 1
            continue
        if ch == "|":
            start = i
            i += 1
            while i < n and text[i] != "|":
                # Quoted symbols are deliberately kept verbatim.  A backslash
                # is not an SMT-LIB escape here, but accepting the following
                # character makes diagnostics friendlier for generated inputs.
                if text[i] == "\\" and i + 1 < n:
                    i += 2
                else:
                    i += 1
            if i >= n:
                raise SExprError(f"unterminated quoted symbol at offset {start}")
            i += 1
            yield Token(text[start:i], start)
            continue
        if ch == '"':
            start = i
            i += 1
            while i < n:
                if text[i] != '"':
                    i += 1
                    continue
                # SMT-LIB escapes a quote inside a string by doubling it.
                if i + 1 < n and text[i + 1] == '"':
                    i += 2
                    continue
                i += 1
                break
            else:
                raise SExprError(f"unterminated string at offset {start}")
            yield Token(text[start:i], start)
            continue

        start = i
        while i < n and not text[i].isspace() and text[i] not in "();":
            i += 1
        yield Token(text[start:i], start)


def parse_commands(text: str) -> list[list[object]]:
    """Parse top-level SMT-LIB commands into lightweight nested Python lists."""

    stack: list[list[object]] = []
    commands: list[list[object]] = []
    for token in tokenize_smt2(text):
        if token.text == "(":
            stack.append([])
        elif token.text == ")":
            if not stack:
                raise SExprError(f"unexpected ')' at offset {token.offset}")
            completed = stack.pop()
            if stack:
                stack[-1].append(completed)
            else:
                commands.append(completed)
        else:
            if not stack:
                raise SExprError(
                    f"token outside a command at offset {token.offset}: {token.text!r}"
                )
            stack[-1].append(token.text)
    if stack:
        raise SExprError("unterminated SMT-LIB command")
    return commands


def unquote_symbol(symbol: str) -> str:
    if len(symbol) >= 2 and symbol[0] == "|" and symbol[-1] == "|":
        return symbol[1:-1]
    return symbol


def declared_relation_names(text: str) -> set[str]:
    """Return all relation declarations in one command-parser pass.

    Both Z3 fixedpoint ``declare-rel`` commands and pure SMT-LIB Bool-valued
    ``declare-fun`` commands denote CHC predicates.
    """
    names: set[str] = set()
    for command in parse_commands(text):
        if len(command) >= 2 and command[0] == "declare-rel":
            name = command[1]
            if not isinstance(name, str):
                raise SExprError("declare-rel name is not a symbol")
            names.add(unquote_symbol(name))
        elif (
            len(command) == 4
            and command[0] == "declare-fun"
            and command[3] == "Bool"
        ):
            name = command[1]
            if not isinstance(name, str):
                raise SExprError("declare-fun name is not a symbol")
            names.add(unquote_symbol(name))
    return names
