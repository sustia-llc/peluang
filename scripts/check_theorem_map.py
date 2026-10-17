#!/usr/bin/env python3
"""Check THEOREM_MAP.md coverage between lean/Peluang/ and tests/formalization_lean/.

Exit 0 when every `theorem`/`lemma` under lean/Peluang/ has a THEOREM_MAP row
whose Rust test exists, or an opt-out `-- WITNESS: none (<reason>)` on the
preceding line; and when every non-`mathlib:` row names a test file that holds
exactly one `/// THEOREM_MAP: <id>` tag directly above a `#[test]` fn of the
named name. Exit 1 otherwise, printing each failure on its own line.

Usage: check_theorem_map.py [REPO_ROOT]
"""

from __future__ import annotations

import re
import sys
from dataclasses import dataclass
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_lean_source import MODIFIERS, strip_code  # noqa: E402

DECL_RE = re.compile(rf"^\s*(?:@\[[^\]]*\]\s*)*{MODIFIERS}(?:theorem|lemma)\s+([A-Za-z_][\w'.]*)")
DECL_KEYWORD_ONLY_RE = re.compile(rf"^\s*(?:@\[[^\]]*\]\s*)*{MODIFIERS}(?:theorem|lemma)\s*$")
NAME_RE = re.compile(r"^\s*([A-Za-z_][\w'.]*)")
ATTR_LINE_RE = re.compile(r"^\s*@\[[^\]]*\]\s*$")
NAMESPACE_RE = re.compile(r"^\s*namespace\s+([\w.]+)")
SECTION_RE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:public|noncomputable)\s+)*section(?:\s+([\w.]+))?\s*$")
MUTUAL_RE = re.compile(r"^\s*mutual\s*$")
END_RE = re.compile(r"^\s*end(?:\s+([\w.]+))?\s*$")
OPT_OUT_RE = re.compile(r"^\s*--\s*WITNESS:\s*none\s*\(.+\)\s*$")
ROW_RE = re.compile(r"^\|\s*(?P<id>[^|]+?)\s*\|\s*(?P<test>[^|]+?)\s*\|\s*(?P<anchor>[^|]*?)\s*\|\s*$")
TEST_REF_RE = re.compile(r"^tests/formalization_lean/(?P<file>[\w/]+\.rs)::(?P<fn>\w+)$")
TAG_RE = re.compile(r"^\s*///\s*THEOREM_MAP:\s*(\S+)\s*$")
TEST_FN_RE = re.compile(r"^\s*(?:pub\s+)?fn\s+(\w+)\s*\(")


@dataclass(frozen=True)
class Decl:
    qualified: str
    path: Path
    line: int
    opted_out: bool


def lean_decls(lean_root: Path) -> list[Decl]:
    decls: list[Decl] = []
    for path in sorted(lean_root.rglob("*.lean")):
        stack: list[tuple[str, str]] = []  # (kind, name); kind is "namespace", "section" or "mutual"
        source = path.read_text(encoding="utf-8")
        raw = source.splitlines()
        lines = strip_code(source).splitlines()
        for i, line in enumerate(lines):
            m = NAMESPACE_RE.match(line)
            if m:
                stack.append(("namespace", m.group(1)))
                continue
            m = SECTION_RE.match(line)
            if m:
                stack.append(("section", m.group(1) or ""))
                continue
            if MUTUAL_RE.match(line):
                stack.append(("mutual", ""))
                continue
            m = END_RE.match(line)
            if m and stack and (m.group(1) is None or m.group(1) == stack[-1][1]):
                stack.pop()
                continue
            name = None
            m = DECL_RE.match(line)
            if m:
                name = m.group(1)
            elif DECL_KEYWORD_ONLY_RE.match(line):
                for follow in lines[i + 1 : i + 3]:
                    fm = NAME_RE.match(follow)
                    if fm:
                        name = fm.group(1)
                        break
            if name is None:
                continue
            namespaces = [name for (kind, name) in stack if kind == "namespace"]
            if name.startswith("_root_."):
                qualified = name.removeprefix("_root_.")
            else:
                qualified = ".".join([*namespaces, name]) if namespaces else name
            j = i - 1
            while j >= 0 and ATTR_LINE_RE.match(raw[j]):
                j -= 1
            opted = j >= 0 and OPT_OUT_RE.match(raw[j]) is not None
            decls.append(Decl(qualified, path, i + 1, opted))
    return decls


def map_rows(map_path: Path) -> tuple[dict[str, tuple[str, int]], list[str]]:
    rows: dict[str, tuple[str, int]] = {}
    duplicates: list[str] = []
    in_table = False
    for i, line in enumerate(map_path.read_text(encoding="utf-8").splitlines()):
        if line.startswith("| Lean id"):
            in_table = True
            continue
        if not in_table or not line.startswith("|"):
            continue
        if re.match(r"^\|\s*-+\s*\|", line):
            continue
        m = ROW_RE.match(line)
        if m:
            lean_id = m.group("id")
            if lean_id in rows:
                duplicates.append(
                    f"THEOREM_MAP.md:{i + 1}: duplicate row for `{lean_id}` (first at line {rows[lean_id][1]})"
                )
                continue
            rows[lean_id] = (m.group("test"), i + 1)
    return rows, duplicates


def tagged_tests(tests_root: Path) -> dict[str, list[tuple[Path, str]]]:
    tags: dict[str, list[tuple[Path, str]]] = {}
    if not tests_root.is_dir():
        return tags
    for path in sorted(tests_root.rglob("*.rs")):
        lines = path.read_text(encoding="utf-8").splitlines()
        for i, line in enumerate(lines):
            m = TAG_RE.match(line)
            if not m:
                continue
            fn_name = ""
            for follow in lines[i + 1 : i + 6]:
                fm = TEST_FN_RE.match(follow)
                if fm:
                    fn_name = fm.group(1)
                    break
            tags.setdefault(m.group(1), []).append((path, fn_name))
    return tags


def check(root: Path) -> list[str]:
    failures: list[str] = []
    map_path = root / "THEOREM_MAP.md"
    if not map_path.is_file():
        return [f"{map_path}: missing"]
    rows, duplicates = map_rows(map_path)
    failures.extend(duplicates)
    tests_root = root / "tests" / "formalization_lean"
    tags = tagged_tests(tests_root)

    lean_root = root / "lean" / "Peluang"
    decls = lean_decls(lean_root) if lean_root.is_dir() else []
    for d in decls:
        if d.opted_out:
            continue
        if d.qualified not in rows:
            failures.append(
                f"{d.path}:{d.line}: `{d.qualified}` has no THEOREM_MAP row and no `-- WITNESS: none (...)` opt-out"
            )

    for lean_id, (test_ref, row_line) in rows.items():
        if lean_id.startswith("mathlib:"):
            continue
        m = TEST_REF_RE.match(test_ref)
        if not m:
            failures.append(f"THEOREM_MAP.md:{row_line}: test column `{test_ref}` is not `tests/formalization_lean/<file>.rs::<fn>`")
            continue
        test_path = root / "tests" / "formalization_lean" / m.group("file")
        if not test_path.is_file():
            failures.append(f"THEOREM_MAP.md:{row_line}: `{test_path}` does not exist")
            continue
        found = [(p, fn) for (p, fn) in tags.get(lean_id, []) if p == test_path]
        if len(found) != 1:
            failures.append(
                f"THEOREM_MAP.md:{row_line}: `{test_path}` carries {len(found)} `/// THEOREM_MAP: {lean_id}` tags; expected exactly 1"
            )
            continue
        if found[0][1] != m.group("fn"):
            failures.append(
                f"THEOREM_MAP.md:{row_line}: tag `{lean_id}` sits above fn `{found[0][1]}`, row names `{m.group('fn')}`"
            )
    return failures


def main(argv: list[str]) -> int:
    root = Path(argv[1]).resolve() if len(argv) > 1 else Path(__file__).resolve().parent.parent
    failures = check(root)
    for f in failures:
        print(f)
    if failures:
        print(f"check_theorem_map: {len(failures)} failure(s)")
        return 1
    print("check_theorem_map: ok")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
