#!/usr/bin/env python3
"""Find `sorry`/`admit` terms and `axiom` declarations in the Lean sources under lean/.

Scans every `*.lean` file under lean/ outside lean/.lake, after blanking line
comments (`--`), nested block comments and docstrings (`/- … -/`), string
literals (`"…"`, raw `r"…"` / `r#"…"#`) and char literals. Exit 0 when none
occurs; exit 1 otherwise, printing `path:line: <kind>` per hit.

Usage: check_lean_source.py [REPO_ROOT]
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

MODIFIERS = r"(?:(?:private|protected|public|noncomputable|unsafe|partial|nonrec)\s+)*"
SORRY_RE = re.compile(r"(?<![\w.'])(sorry|admit)(?![\w'])")
CHAR_RE = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^\\'\n])'")
RAW_RE = re.compile(r'r(#*)"')
AXIOM_RE = re.compile(rf"^\s*(?:@\[[^\]]*\]\s*)*{MODIFIERS}axiom\b")


def strip_code(src: str) -> str:
    """Return `src` with comments and string literals replaced by spaces, newlines kept."""
    out: list[str] = []
    i, n, depth = 0, len(src), 0
    in_string = False
    while i < n:
        c = src[i]
        nxt = src[i + 1] if i + 1 < n else ""
        if depth > 0:
            if c == "/" and nxt == "-":
                depth += 1
                out.append("  ")
                i += 2
            elif c == "-" and nxt == "/":
                depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif in_string:
            if c == "\\" and nxt:
                out.append("  " if nxt != "\n" else " \n")
                i += 2
            else:
                if c == '"':
                    in_string = False
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif c == "/" and nxt == "-":
            depth = 1
            out.append("  ")
            i += 2
        elif c == "-" and nxt == "-":
            while i < n and src[i] != "\n":
                out.append(" ")
                i += 1
        elif c == '"':
            in_string = True
            out.append(" ")
            i += 1
        elif c in "'r" and not (i > 0 and (src[i - 1].isalnum() or src[i - 1] in "_'.")):
            m = (CHAR_RE if c == "'" else RAW_RE).match(src, i)
            if m is None:
                out.append(c)
                i += 1
                continue
            end = m.end()
            if c == "r":
                close = src.find('"' + m.group(1), end)
                end = n if close < 0 else close + 1 + len(m.group(1))
            out.append(re.sub(r"[^\n]", " ", src[i:end]))
            i = end
        else:
            out.append(c)
            i += 1
    return "".join(out)


def scan(text: str) -> list[tuple[int, str]]:
    hits: list[tuple[int, str]] = []
    for lineno, line in enumerate(strip_code(text).splitlines(), start=1):
        for m in SORRY_RE.finditer(line):
            hits.append((lineno, m.group(1)))
        if AXIOM_RE.match(line):
            hits.append((lineno, "axiom declaration"))
    return hits


def check(root: Path) -> list[str]:
    lean = root / "lean"
    failures: list[str] = []
    for path in sorted(lean.rglob("*.lean")) if lean.is_dir() else []:
        if ".lake" in path.relative_to(lean).parts:
            continue
        for lineno, kind in scan(path.read_text(encoding="utf-8")):
            failures.append(f"{path.relative_to(root)}:{lineno}: {kind}")
    return failures


def main(argv: list[str]) -> int:
    root = Path(argv[1]).resolve() if len(argv) > 1 else Path(__file__).resolve().parent.parent
    failures = check(root)
    for f in failures:
        print(f)
    if failures:
        print(f"check_lean_source: {len(failures)} hit(s)")
        return 1
    print("check_lean_source: ok")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
