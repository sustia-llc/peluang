#!/usr/bin/env python3
"""Check a `lake build` log for warning lines and for the `peluangTest` audit line.

Reads the file at LOG as UTF-8, undecodable bytes replaced, splits it into
lines at `\\n` and removes one trailing `\\r` from each line. A warning line is
a line that contains `warning:`. An audit line is a line that starts with
`info: PeluangTest/Audit.lean:<n>:<n>: peluangTest audit: <n> files, <n> imported`.
Exit 0 when the log has no warning line and exactly one audit line, printing
`check_lake_log: ok (1 audit line, 0 warning lines)`; exit 1 otherwise,
printing `LOG:line: <the line>` per warning line, then
`LOG: <n> audit line(s), expected exactly 1` when the count is not 1, then
`check_lake_log: failed (<n> warning line(s), <n> audit line(s))`; or, when
the file cannot be read, `LOG: missing` / `LOG: not readable: <error>`, then
`check_lake_log: failed (log not read)`; exit 2, printing the usage line on
stderr, when the argument count is not 1. A character that stdout cannot
encode is printed as a backslash escape.

Usage: check_lake_log.py LOG
"""

from __future__ import annotations

import re
import sys

USAGE = "Usage: check_lake_log.py LOG"
WARNING = "warning:"
AUDIT_RE = re.compile(r"info: PeluangTest/Audit\.lean:[0-9]+:[0-9]+: peluangTest audit: [0-9]+ files, [0-9]+ imported")


def scan(text: str) -> tuple[list[tuple[int, str]], int]:
    """The (line number, line) pairs of the lines of `text` that contain `warning:`, in line order, and the
    number of lines that `AUDIT_RE` matches at their start. Lines are the pieces of `text` between `\\n`, each
    with one trailing `\\r` removed."""
    warnings: list[tuple[int, str]] = []
    audits = 0
    for lineno, line in enumerate(text.split("\n"), start=1):
        line = line.removesuffix("\r")
        if WARNING in line:
            warnings.append((lineno, line))
        if AUDIT_RE.match(line):
            audits += 1
    return warnings, audits


def read(log: str) -> tuple[str | None, str | None]:
    """The text of the file at the path `log`, decoded as UTF-8 with undecodable bytes replaced, and `None`;
    or `None` and the failure line when the file is missing or not readable."""
    try:
        with open(log, "rb") as handle:
            return handle.read().decode("utf-8", errors="replace"), None
    except FileNotFoundError:
        return None, f"{log}: missing"
    except OSError as exc:
        return None, f"{log}: not readable: {exc.strerror or exc}"


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print(USAGE, file=sys.stderr)
        return 2
    reconfigure = getattr(sys.stdout, "reconfigure", None)
    if reconfigure is not None:
        reconfigure(errors="backslashreplace")
    log = argv[1]
    text, failure = read(log)
    if text is None:
        print(failure)
        print("check_lake_log: failed (log not read)")
        return 1
    warnings, audits = scan(text)
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
