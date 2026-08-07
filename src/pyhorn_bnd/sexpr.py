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


def requires_general_smt_parser(text: str) -> bool:
    """Return whether the fixedpoint parser lacks a declared theory sort.

    Z3's fixedpoint command parser does not currently accept the SMT-LIB
    string/sequence sort family.  The general parser does.  String literals do
    not trigger this check because their complete token includes quotes.
    """

    unsupported_sort_tokens = {
        "Char",
        "RegEx",
        "RegLan",
        "Seq",
        "String",
        "Unicode",
    }
    return any(
        token.text in unsupported_sort_tokens for token in tokenize_smt2(text)
    )


def render_sexpr(expression: object) -> str:
    """Render a command-parser node back to SMT-LIB syntax.

    Tokens produced by :func:`tokenize_smt2` retain quoted symbols and string
    literals verbatim, so this renderer only has to restore parentheses and
    whitespace.  It is intentionally small and is not a semantic SMT-LIB
    pretty-printer.
    """

    if isinstance(expression, list):
        return "(" + " ".join(render_sexpr(item) for item in expression) + ")"
    if not isinstance(expression, str):
        raise SExprError(f"unsupported SMT-LIB node: {expression!r}")
    return expression


@dataclass(frozen=True)
class GeneralSmt2Input:
    """Pure SMT-LIB text plus marker assertions for fixedpoint queries."""

    text: str
    query_count: int


def to_general_smt2(text: str) -> GeneralSmt2Input:
    """Translate Z3 fixedpoint commands into ordinary SMT-LIB assertions.

    Z3's general SMT-LIB parser supports theories, including strings and
    sequences, that are not accepted by the fixedpoint command parser.  This
    translation preserves the CHC formulas while converting:

    - ``declare-rel`` to Bool-valued ``declare-fun``;
    - ``declare-var`` declarations to universal binders on each rule/assert;
    - ``rule`` to ``assert``; and
    - ``query`` to trailing marker assertions used only to recover the queried
      nullary relation declarations.

    Pure SMT-LIB files pass through unchanged except that terminal commands
    such as ``check-sat`` are omitted from the parser input.
    """

    commands = parse_commands(text)
    declared_variables: list[list[object]] = []
    output: list[list[object]] = []
    query_markers: list[object] = []

    ignored_commands = {
        "check-sat",
        "check-sat-assuming",
        "get-assertions",
        "get-assignment",
        "get-info",
        "get-model",
        "get-option",
        "get-proof",
        "get-unsat-assumptions",
        "get-unsat-core",
        "get-value",
        "exit",
        "push",
        "pop",
        "reset",
        "reset-assertions",
    }

    for command in commands:
        if not command:
            continue
        operator = command[0]
        if not isinstance(operator, str):
            raise SExprError("SMT-LIB command name is not a symbol")

        if operator == "declare-var":
            if len(command) != 3 or not isinstance(command[1], str):
                raise SExprError("malformed declare-var command")
            declared_variables.append([command[1], command[2]])
            continue

        if operator == "declare-rel":
            if (
                len(command) != 3
                or not isinstance(command[1], str)
                or not isinstance(command[2], list)
            ):
                raise SExprError("malformed declare-rel command")
            output.append(["declare-fun", command[1], command[2], "Bool"])
            continue

        if operator in {"rule", "assert"}:
            if len(command) < 2:
                raise SExprError(f"malformed {operator} command")
            formula: object = command[1]
            if declared_variables:
                # Copy the binder list because command nodes are mutable lists.
                formula = [
                    "forall",
                    [list(binding) for binding in declared_variables],
                    formula,
                ]
            output.append(["assert", formula])
            continue

        if operator == "query":
            if len(command) < 2:
                raise SExprError("malformed query command")
            query_markers.append(command[1])
            continue

        if operator == "set-option" and len(command) >= 2:
            option = command[1]
            if isinstance(option, str) and option.startswith(
                (":fixedpoint.", ":fp.")
            ):
                # Fixedpoint-engine parameters are irrelevant after translating
                # rules to ordinary assertions and are rejected by the general
                # SMT parser as unknown modules.
                continue

        if operator in ignored_commands:
            continue

        output.append(command)

    # Query markers are parsed as ordinary assertions and removed immediately
    # afterward.  Queries are currently required to be nullary relation
    # applications, so no synthetic arguments are needed.
    output.extend(["assert", marker] for marker in query_markers)
    rendered = "\n".join(render_sexpr(command) for command in output)
    return GeneralSmt2Input(
        text=rendered + ("\n" if rendered else ""),
        query_count=len(query_markers),
    )
