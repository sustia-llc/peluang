#!/usr/bin/env python3
"""Check a `lake build` log for warning lines and for the audit line of the test library.

Reads `REPO_ROOT/lean/lakefile.lean` and takes the test library name `<T>`
from it. REPO_ROOT defaults to the parent of the folder of this script. A
library line is a line that, with its comments replaced by spaces, holds
optional white space, zero or more attributes `@[…]`, `lean_lib`, white space,
and a name written `«<name>»` or as a run of characters with no white space.
`<T>` is the name of the one library line whose name ends in `Test`, and it is
a letter followed by letters, digits or `_`; `<t>` is `<T>` with its first
letter in lower case. A comment is a `--` line comment or a `/- … -/` block
comment, which nests; a `"…"` string literal with `\\` as its escape character
holds no comment. A char literal and a raw string literal are read as code,
so a `"` in one of them starts a string literal.

Reads the file at LOG as UTF-8, undecodable bytes replaced, and splits it into
lines at `\\n`. It removes each control sequence from a line: `ESC [`, then
bytes from `0` to `?`, then bytes from space to `/`, then one byte from `@`
to `~`. It then splits the line into pieces at `\\r`. A warning is a piece
that contains `warning:`, or the line itself when it contains `warning:` and
no piece does. An audit piece starts with
`info: <T>/Audit.lean:<n>:<n>: <t> audit: <n> files, <n> imported`.

Exit 0 when the log has no warning and exactly one audit piece, printing
`check_lake_log: ok (1 audit line, 0 warning lines)`; exit 1 otherwise,
printing `LOG:line: <the text>` per warning, then
`LOG: <n> audit line(s), expected exactly 1` when the count is not 1, then
`check_lake_log: failed (<n> warning line(s), <n> audit line(s))`; or, when
the log cannot be read, `LOG: missing` / `LOG: not readable: <error>`, then
`check_lake_log: failed (log not read)`; or, when the lakefile cannot be read,
has a number of library lines with a name that ends in `Test` other than 1, or
has such a name that is not a letter followed by letters, digits or `_`, one
line that names the lakefile, then
`check_lake_log: failed (test library name not read)`; exit 2, printing the
usage line on stderr, when the argument count is not 1 or 2. While it runs, a
character that stdout cannot encode is printed as a backslash escape.

Usage: check_lake_log.py LOG [REPO_ROOT]
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

USAGE = "Usage: check_lake_log.py LOG [REPO_ROOT]"
WARNING = "warning:"
SUFFIX = "Test"
LIB_RE = re.compile(r"\s*(?:@\[[^\]]*\]\s*)*lean_lib\s+(?:«(?P<quoted>[^»]*)»|(?P<bare>\S+))")
NAME_RE = re.compile(r"[A-Za-z][A-Za-z0-9_]*")
CSI_RE = re.compile(r"\x1b\[[0-?]*[ -/]*[@-~]")


def read(path: str) -> tuple[str | None, str | None]:
    """The text of the file at `path`, decoded as UTF-8 with undecodable bytes replaced, and `None`; or `None`
    and the failure line when the file is missing or not readable."""
    try:
        with open(path, "rb") as handle:
            return handle.read().decode("utf-8", errors="replace"), None
    except FileNotFoundError:
        return None, f"{path}: missing"
    except OSError as exc:
        return None, f"{path}: not readable: {exc.strerror or exc}"


def strip_comments(src: str) -> str:
    """`src` with each character of a `--` line comment and of a `/- … -/` block comment replaced by a space,
    newlines kept. Block comments nest. A `"…"` string literal, with `\\` as its escape character, is kept
    and holds no comment. A `"` outside a comment and a string literal starts a string literal, also inside
    a char literal or a raw string literal. A block comment with no end runs to the end of `src`."""
    out: list[str] = []
    i, depth, in_string = 0, 0, False
    while i < len(src):
        two = src[i : i + 2]
        if depth:
            if two == "/-":
                depth += 1
            elif two == "-/":
                depth -= 1
            if two in ("/-", "-/"):
                out.append("  ")
                i += 2
            else:
                out.append("\n" if src[i] == "\n" else " ")
                i += 1
        elif in_string:
            if src[i] == "\\":
                out.append(two)
                i += 2
            else:
                in_string = src[i] != '"'
                out.append(src[i])
                i += 1
        elif two == "/-":
            depth = 1
            out.append("  ")
            i += 2
        elif two == "--":
            end = src.find("\n", i)
            end = len(src) if end == -1 else end
            out.append(" " * (end - i))
            i = end
        else:
            in_string = src[i] == '"'
            out.append(src[i])
            i += 1
    return "".join(out)


def test_library(lakefile: str) -> tuple[str | None, str | None]:
    """The test library name of the Lake configuration file at `lakefile` and `None`; or `None` and the
    failure line. A library line is a line of `strip_comments` of the file that holds optional white space,
    zero or more attributes `@[…]`, `lean_lib`, white space, and a name: the text between `«` and `»`, or else
    the text up to the next white space. The test
    library name is the name of the one library line whose name ends in `Test`. It is a failure when the file
    cannot be read, when the number of such lines is not 1, and when the name is not a letter followed by
    letters, digits or `_`."""
    text, failure = read(lakefile)
    if text is None:
        return None, failure
    found: list[tuple[int, str]] = []
    for lineno, line in enumerate(strip_comments(text).split("\n"), start=1):
        match = LIB_RE.match(line)
        if match:
            name = match.group("quoted") if match.group("quoted") is not None else match.group("bare")
            if name.endswith(SUFFIX):
                found.append((lineno, name))
    if len(found) != 1:
        return (
            None,
            f"{lakefile}: {len(found)} lean_lib line(s) with a name that ends in `{SUFFIX}`, expected exactly 1",
        )
    lineno, name = found[0]
    if not NAME_RE.fullmatch(name):
        return None, f"{lakefile}:{lineno}: library name `{name}` is not a letter followed by letters, digits or `_`"
    return name, None


def audit_re(name: str) -> re.Pattern[str]:
    """The pattern of the start of the audit line of the test library `name`:
    `info: <name>/Audit.lean:<n>:<n>: <name with a lower-case first letter> audit: <n> files, <n> imported`."""
    lower = name[0].lower() + name[1:]
    return re.compile(
        rf"info: {re.escape(name)}/Audit\.lean:[0-9]+:[0-9]+: {re.escape(lower)} audit: [0-9]+ files, [0-9]+ imported"
    )


def scan(text: str, audit: re.Pattern[str]) -> tuple[list[tuple[int, str]], int]:
    """The (line number, text) pairs of the warnings of `text`, in order, and the number of pieces that
    `audit` matches at their start. Lines are the parts of `text` between `\\n`. The pieces of a line are its
    parts between `\\r`, after each match of `CSI_RE` is removed from the line. The warnings of a line are
    its pieces that contain `warning:`; when no piece does and the line itself contains `warning:`, the
    one warning is the line with one trailing `\\r` removed."""
    warnings: list[tuple[int, str]] = []
    audits = 0
    for lineno, line in enumerate(text.split("\n"), start=1):
        pieces = CSI_RE.sub("", line).split("\r")
        hits = [piece for piece in pieces if WARNING in piece]
        if not hits and WARNING in line:
            hits = [line.removesuffix("\r")]
        warnings.extend((lineno, hit) for hit in hits)
        audits += sum(1 for piece in pieces if audit.match(piece))
    return warnings, audits


def report(log: str, root: Path) -> int:
    name, failure = test_library(str(root / "lean" / "lakefile.lean"))
    if name is None:
        print(failure)
        print("check_lake_log: failed (test library name not read)")
        return 1
    text, failure = read(log)
    if text is None:
        print(failure)
        print("check_lake_log: failed (log not read)")
        return 1
    warnings, audits = scan(text, audit_re(name))
    for lineno, piece in warnings:
        print(f"{log}:{lineno}: {piece}")
    if audits != 1:
        print(f"{log}: {audits} audit line(s), expected exactly 1")
    if warnings or audits != 1:
        print(f"check_lake_log: failed ({len(warnings)} warning line(s), {audits} audit line(s))")
        return 1
    print("check_lake_log: ok (1 audit line, 0 warning lines)")
    return 0


def main(argv: list[str]) -> int:
    if len(argv) not in (2, 3):
        print(USAGE, file=sys.stderr)
        return 2
    root = Path(argv[2]) if len(argv) == 3 else Path(__file__).resolve().parent.parent
    stdout = sys.stdout
    reconfigure = getattr(stdout, "reconfigure", None)
    if reconfigure is None:
        return report(argv[1], root)
    errors = stdout.errors
    reconfigure(errors="backslashreplace")
    try:
        return report(argv[1], root)
    finally:
        stdout.flush()
        reconfigure(errors=errors)


if __name__ == "__main__":
    sys.exit(main(sys.argv))
