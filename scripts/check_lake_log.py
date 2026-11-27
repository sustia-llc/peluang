#!/usr/bin/env python3
"""Check a `lake build` log for warning lines and for the `peluangTest` audit line.

Reads the file at LOG as UTF-8, undecodable bytes replaced, and splits it into
lines at `\\n`. Exit 0 when no line contains `warning:` and exactly one line
matches `peluangTest audit: [0-9]+ files`, printing
`check_lake_log: ok (1 audit line, 0 warning lines)`; exit 1 otherwise,
printing `LOG:line: <the line>` per warning line, then
`LOG: <n> audit line(s), expected exactly 1` when the count is not 1, or
`LOG: missing` / `LOG: not readable: <error>` alone when the file cannot be
read, then the number of failures; exit 2, printing the usage line on stderr,
when the argument count is not 1.

Usage: check_lake_log.py LOG
"""

from __future__ import annotations

import re
import sys

USAGE = "Usage: check_lake_log.py LOG"
WARNING = "warning:"
AUDIT_RE = re.compile(r"peluangTest audit: [0-9]+ files")


def scan(text: str) -> tuple[list[tuple[int, str]], int]:
    """The (line number, line) pairs of the lines of `text` that contain `warning:`, in line order, and the
    number of lines that match `peluangTest audit: [0-9]+ files`. Lines are the pieces of `text` between `\\n`."""
    warnings: list[tuple[int, str]] = []
    audits = 0
    for lineno, line in enumerate(text.split("\n"), start=1):
        if WARNING in line:
            warnings.append((lineno, line))
        if AUDIT_RE.search(line):
            audits += 1
    return warnings, audits


def check(log: str) -> list[str]:
    """The failures of the `lake build` log at the path `log`: the file is missing or not readable; else each
    warning line as `log:line: <the line>`, then the audit line count when it is not 1."""
    try:
        with open(log, "rb") as handle:
            text = handle.read().decode("utf-8", errors="replace")
    except FileNotFoundError:
        return [f"{log}: missing"]
    except OSError as exc:
        return [f"{log}: not readable: {exc.strerror or exc}"]
    warnings, audits = scan(text)
    failures = [f"{log}:{lineno}: {line}" for lineno, line in warnings]
    if audits != 1:
        failures.append(f"{log}: {audits} audit line(s), expected exactly 1")
    return failures


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print(USAGE, file=sys.stderr)
        return 2
    failures = check(argv[1])
    for f in failures:
        print(f)
    if failures:
        print(f"check_lake_log: {len(failures)} failure(s)")
        return 1
    print("check_lake_log: ok (1 audit line, 0 warning lines)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
