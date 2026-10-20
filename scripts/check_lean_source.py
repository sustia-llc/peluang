#!/usr/bin/env python3
"""Find `sorry`/`admit`/`native_decide`/`decide +native` terms and `axiom`
declarations in the Lean sources under lean/, and `theorem`/`lemma`
declarations under lean/PeluangTest/.

Scans every `*.lean` file under lean/ outside lean/.lake, after blanking line
comments (`--`), nested block comments and docstrings (`/- … -/`), string
literals (`"…"`, raw `r"…"` / `r#"…"#`; the `{…}` holes of `s!`/`m!`/`f!`
strings stay code) and char literals. Exit 0 when none occurs; exit 1
otherwise, printing `path:line: <kind>` per hit.

Usage: check_lean_source.py [REPO_ROOT]
"""

from __future__ import annotations

import os
import re
import sys
from pathlib import Path

MODIFIERS = r"(?:(?:private|protected|public|noncomputable|unsafe|partial|nonrec)\s+)*"
PREFIX = r"(?:(?:open|set_option)\b[^\n]*?\bin\s+)*(?:@\[[^\]]*\]\s*)*"
SORRY_RE = re.compile(r"(?<![\w.'`«])(sorry|admit|native_decide)(?![\w'»])")
DECIDE_NATIVE_RE = re.compile(r"(?<![\w.'`«])decide\s*\+native(?![\w'»])")
CHAR_RE = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^\\'\n])'")
RAW_RE = re.compile(r'r(#*)"')
AXIOM_RE = re.compile(rf"^\s*{PREFIX}{MODIFIERS}axiom\b")
THEOREM_RE = re.compile(rf"^\s*{PREFIX}{MODIFIERS}(?:theorem|lemma)\b")
TEST_DIR = "PeluangTest"


def strip_code(src: str) -> str:
    """Return `src` with comments and string literals replaced by spaces, newlines kept."""
    out: list[str] = []
    i, n, depth = 0, len(src), 0
    # frames: ("code", brace depth) or ("str", interpolated); bottom frame is code.
    frames: list[tuple[str, int]] = [("code", 0)]
    while i < n:
        c = src[i]
        nxt = src[i + 1] if i + 1 < n else ""
        kind, val = frames[-1]
        in_string = kind == "str"
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
                    frames.pop()
                elif c == "{" and val:
                    frames.append(("code", 0))
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif c == "}" and len(frames) > 1:
            if val == 0:
                frames.pop()
            else:
                frames[-1] = ("code", val - 1)
            out.append(" " if val == 0 else c)
            i += 1
        elif c == "{" and len(frames) > 1:
            frames[-1] = ("code", val + 1)
            out.append(c)
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
            frames.append(("str", int(i > 0 and src[i - 1] == "!")))
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


def scan(text: str, test_file: bool = False) -> list[tuple[int, str]]:
    hits: list[tuple[int, str]] = []
    for lineno, line in enumerate(strip_code(text).splitlines(), start=1):
        for m in SORRY_RE.finditer(line):
            hits.append((lineno, m.group(1)))
        for _ in DECIDE_NATIVE_RE.finditer(line):
            hits.append((lineno, "decide +native"))
        if AXIOM_RE.match(line):
            hits.append((lineno, "axiom declaration"))
        if test_file and THEOREM_RE.match(line):
            hits.append((lineno, "theorem/lemma in the test library"))
    return hits


def lean_sources(lean: Path) -> list[Path]:
    found: list[Path] = []
    for dirpath, dirnames, filenames in os.walk(lean):
        dirnames[:] = [d for d in dirnames if d != ".lake"]
        found.extend(Path(dirpath) / f for f in filenames if f.endswith(".lean"))
    return sorted(found)


def check(root: Path) -> list[str]:
    lean = root / "lean"
    failures: list[str] = []
    for path in lean_sources(lean) if lean.is_dir() else []:
        test_file = path.relative_to(lean).parts[0] in (TEST_DIR, f"{TEST_DIR}.lean")
        for lineno, kind in scan(path.read_text(encoding="utf-8"), test_file):
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
