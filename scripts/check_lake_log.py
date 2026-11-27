#!/usr/bin/env python3
"""Check a `lake build` log for warning lines and for the audit line of the test library.

Reads `REPO_ROOT/lean/lakefile.lean` and takes the package name `<L>` from its
one line that starts with `package`, written `package «<L>»` or `package <L>`;
`<l>` is `<L>` with its first letter in lower case. REPO_ROOT defaults to the
parent of the folder of this script. Reads the file at LOG as UTF-8,
undecodable bytes replaced, splits it into lines at `\\n` and removes one
trailing `\\r` from each line. A warning line is a line that contains
`warning:`. An audit line is a line that starts with
`info: <L>Test/Audit.lean:<n>:<n>: <l>Test audit: <n> files, <n> imported`.
Exit 0 when the log has no warning line and exactly one audit line, printing
`check_lake_log: ok (1 audit line, 0 warning lines)`; exit 1 otherwise,
printing `LOG:line: <the line>` per warning line, then
`LOG: <n> audit line(s), expected exactly 1` when the count is not 1, then
`check_lake_log: failed (<n> warning line(s), <n> audit line(s))`; or, when
the log cannot be read, `LOG: missing` / `LOG: not readable: <error>`, then
`check_lake_log: failed (log not read)`; or, when the lakefile cannot be read,
has a number of `package` lines other than 1, or has a package name that is
not a letter followed by letters, digits or `_`, one line that names the
lakefile, then `check_lake_log: failed (package name not read)`; exit 2,
printing the usage line on stderr, when the argument count is not 1 or 2. A
character that stdout cannot encode is printed as a backslash escape.

Usage: check_lake_log.py LOG [REPO_ROOT]
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

USAGE = "Usage: check_lake_log.py LOG [REPO_ROOT]"
WARNING = "warning:"
PACKAGE_RE = re.compile(r"package\s+(?:«(?P<quoted>[^»]*)»|(?P<bare>\S+))")
NAME_RE = re.compile(r"[A-Za-z][A-Za-z0-9_]*")


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


def package_name(lakefile: str) -> tuple[str | None, str | None]:
    """The package name of the Lake configuration file at `lakefile` and `None`; or `None` and the failure
    line. The name is the text between `«` and `»`, or else the text up to the next white space, after
    `package` and white space at the start of a line. It is a failure when the file cannot be read, when the
    number of such lines is not 1, and when the name is not a letter followed by letters, digits or `_`."""
    text, failure = read(lakefile)
    if text is None:
        return None, failure
    found = [(n, m) for n, line in enumerate(text.split("\n"), start=1) if (m := PACKAGE_RE.match(line))]
    if len(found) != 1:
        return None, f"{lakefile}: {len(found)} package line(s), expected exactly 1"
    lineno, match = found[0]
    name = match.group("quoted") if match.group("quoted") is not None else match.group("bare")
    if not NAME_RE.fullmatch(name):
        return None, f"{lakefile}:{lineno}: package name `{name}` is not a letter followed by letters, digits or `_`"
    return name, None


def audit_re(name: str) -> re.Pattern[str]:
    """The pattern of the start of the audit line of the package `name`:
    `info: <name>Test/Audit.lean:<n>:<n>: <name with a lower-case first letter>Test audit: <n> files, <n> imported`."""
    lower = name[0].lower() + name[1:]
    return re.compile(
        rf"info: {re.escape(name)}Test/Audit\.lean:[0-9]+:[0-9]+: {re.escape(lower)}Test audit: [0-9]+ files, [0-9]+ imported"
    )


def scan(text: str, audit: re.Pattern[str]) -> tuple[list[tuple[int, str]], int]:
    """The (line number, line) pairs of the lines of `text` that contain `warning:`, in line order, and the
    number of lines that `audit` matches at their start. Lines are the pieces of `text` between `\\n`, each
    with one trailing `\\r` removed."""
    warnings: list[tuple[int, str]] = []
    audits = 0
    for lineno, line in enumerate(text.split("\n"), start=1):
        line = line.removesuffix("\r")
        if WARNING in line:
            warnings.append((lineno, line))
        if audit.match(line):
            audits += 1
    return warnings, audits


def main(argv: list[str]) -> int:
    if len(argv) not in (2, 3):
        print(USAGE, file=sys.stderr)
        return 2
    reconfigure = getattr(sys.stdout, "reconfigure", None)
    if reconfigure is not None:
        reconfigure(errors="backslashreplace")
    log = argv[1]
    root = Path(argv[2]) if len(argv) == 3 else Path(__file__).resolve().parent.parent
    name, failure = package_name(str(root / "lean" / "lakefile.lean"))
    if name is None:
        print(failure)
        print("check_lake_log: failed (package name not read)")
        return 1
    text, failure = read(log)
    if text is None:
        print(failure)
        print("check_lake_log: failed (log not read)")
        return 1
    warnings, audits = scan(text, audit_re(name))
    for lineno, line in warnings:
        print(f"{log}:{lineno}: {line}")
    if audits != 1:
        print(f"{log}: {audits} audit line(s), expected exactly 1")
    if warnings or audits != 1:
        print(f"check_lake_log: failed ({len(warnings)} warning line(s), {audits} audit line(s))")
        return 1
    print("check_lake_log: ok (1 audit line, 0 warning lines)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
