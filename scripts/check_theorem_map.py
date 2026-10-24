#!/usr/bin/env python3
"""Check THEOREM_MAP.md coverage between the Peluang library and tests/formalization_lean/.

The library is lean/Peluang.lean plus every file under lean/Peluang/. Exit 0
when every `theorem`/`lemma` in it has a THEOREM_MAP row whose Rust test
exists, or an opt-out `-- WITNESS: none (<reason>)` separated from the
declaration only by blank lines, comments, docstrings and attributes; and when
every non-`mathlib:` row names a test file that holds
exactly one `/// THEOREM_MAP: <id>` tag on a fn of the named name, and when
every tag under tests/formalization_lean/ is placed as follows: the line after
it is `#[test]` or `#[<path>::test]` / `#[<path>::test(...)]` (a trailing `//`
comment allowed), the first line after that which is not blank, a `//`/`///`
comment other than a tag, or a single-line `#[...]` attribute is the `fn`, and
no attribute line in between is `#[ignore]`, `#[should_panic]` or a `cfg` that
names `f64-prob` other than `not(feature = "f64-prob")`. Exit 1 otherwise,
printing each failure (each misplaced tag with its file and line) on its own
line.

Usage: check_theorem_map.py [REPO_ROOT]
"""

from __future__ import annotations

import re
import sys
from dataclasses import dataclass
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_lean_source import MODIFIERS, PREFIX, strip_code  # noqa: E402

COMPONENT = r"(?:[A-Za-z_][\w'!?]*|«[^»\n]*»)"
NAME = rf"{COMPONENT}(?:\.{COMPONENT})*"
DECL_RE = re.compile(rf"^\s*{PREFIX}{MODIFIERS}(?:theorem|lemma)\s+({NAME})")
DECL_KEYWORD_ONLY_RE = re.compile(rf"^\s*{PREFIX}{MODIFIERS}(?:theorem|lemma)\s*$")
NAME_RE = re.compile(rf"^\s*({NAME})")
ATTR_START_RE = re.compile(r"^\s*@\[")
NAMESPACE_RE = re.compile(r"^\s*namespace\s+([\w.]+)")
SECTION_RE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:public|noncomputable)\s+)*section(?:\s+([\w.]+))?\s*$")
MUTUAL_RE = re.compile(r"^\s*mutual\s*$")
END_RE = re.compile(r"^\s*end(?:\s+([\w.]+))?\s*$")
OPT_OUT_RE = re.compile(r"^\s*--\s*WITNESS:\s*none\s*\(.+\)\s*$")
ROW_RE = re.compile(r"^\|\s*(?P<id>[^|]+?)\s*\|\s*(?P<test>[^|]+?)\s*\|\s*(?P<anchor>[^|]*?)\s*\|\s*$")
TEST_REF_RE = re.compile(r"^tests/formalization_lean/(?P<file>[\w/]+\.rs)::(?P<fn>\w+)$")
TAG_RE = re.compile(r"^\s*///\s*THEOREM_MAP:\s*(\S+)\s*$")
TEST_FN_RE = re.compile(
    r"^\s*(?:pub(?:\s*\([^)]*\)\s*|\s+))?(?:const\s+)?(?:async\s+)?(?:extern(?:\s+\"[^\"]*\")?\s+)?"
    r"fn\s+(\w+)\s*[<(]"
)
TEST_ATTR_RE = re.compile(r"^\s*#\[(?:test|(?:\w+::)+test(?:\(.*\))?)\]\s*(?://.*)?$")
BETWEEN_RE = re.compile(r"^\s*(?:#\[.*\]\s*(?://.*)?|//.*)?$")
NOT_RUN_RE = re.compile(r"^\s*#\[\s*(?:ignore|should_panic)\b")
CFG_F64_RE = re.compile(r"^\s*#\[\s*cfg\b.*f64-prob")
CFG_NOT_F64 = 'not(feature="f64-prob")'


def blocking_attr(line: str) -> bool:
    if NOT_RUN_RE.match(line):
        return True
    return bool(CFG_F64_RE.match(line)) and CFG_NOT_F64 not in line.replace(" ", "")


@dataclass(frozen=True)
class Decl:
    qualified: str
    path: Path
    line: int
    opted_out: bool


def library_files(lean_dir: Path, name: str = "Peluang") -> list[Path]:
    root = lean_dir / f"{name}.lean"
    lib = lean_dir / name
    return ([root] if root.is_file() else []) + (sorted(lib.rglob("*.lean")) if lib.is_dir() else [])


def library_decls(lean_dir: Path) -> list[Decl]:
    return lean_decls(library_files(lean_dir))


def attribute_lines(lines: list[str]) -> set[int]:
    """Indices of lines forming an `@[…]` block alone on its lines (comments already stripped)."""
    marked: set[int] = set()
    i = 0
    while i < len(lines):
        if not ATTR_START_RE.match(lines[i]):
            i += 1
            continue
        depth, j, rest = 0, i, None
        while j < len(lines) and rest is None:
            for k, ch in enumerate(lines[j]):
                depth += (ch == "[") - (ch == "]")
                if depth == 0 and ch == "]":
                    rest = lines[j][k + 1 :]
                    break
            if rest is None:
                j += 1
        if rest is not None and not rest.strip():
            marked.update(range(i, j + 1))
        i = j + 1
    return marked


def lean_decls(paths: list[Path]) -> list[Decl]:
    decls: list[Decl] = []
    for path in paths:
        stack: list[tuple[str, str]] = []  # (kind, name); kind is "namespace", "section" or "mutual"
        source = path.read_text(encoding="utf-8")
        raw = source.splitlines()
        lines = strip_code(source).splitlines()
        attrs = attribute_lines(lines)
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
            qualified = qualified.replace("«", "").replace("»", "")
            opted = False
            j = i - 1
            while j >= 0 and (not lines[j].strip() or j in attrs):
                if OPT_OUT_RE.match(raw[j]):
                    opted = True
                    break
                j -= 1
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


def tagged_tests(tests_root: Path) -> tuple[dict[str, list[tuple[Path, str]]], list[str]]:
    tags: dict[str, list[tuple[Path, str]]] = {}
    misplaced: list[str] = []
    if not tests_root.is_dir():
        return tags, misplaced
    for path in sorted(tests_root.rglob("*.rs")):
        lines = path.read_text(encoding="utf-8").splitlines()
        for i, line in enumerate(lines):
            m = TAG_RE.match(line)
            if not m:
                continue
            fm = None
            blocking: list[str] = []
            if i + 1 < len(lines) and TEST_ATTR_RE.match(lines[i + 1]):
                j = i + 2
                while j < len(lines) and BETWEEN_RE.match(lines[j]) and not TAG_RE.match(lines[j]):
                    if blocking_attr(lines[j]):
                        blocking.append(lines[j].strip())
                    j += 1
                fm = TEST_FN_RE.match(lines[j]) if j < len(lines) else None
            if fm and blocking:
                misplaced.append(
                    f"{path}:{i + 1}: `/// THEOREM_MAP: {m.group(1)}` sits on a test that does not run in the exact "
                    f"lane or does not assert: {', '.join(f'`{b}`' for b in blocking)}"
                )
            elif fm:
                tags.setdefault(m.group(1), []).append((path, fm.group(1)))
            else:
                misplaced.append(
                    f"{path}:{i + 1}: `/// THEOREM_MAP: {m.group(1)}` is not on the line directly above "
                    "`#[test]` on a fn"
                )
    return tags, misplaced


def check(root: Path) -> list[str]:
    failures: list[str] = []
    map_path = root / "THEOREM_MAP.md"
    if not map_path.is_file():
        return [f"{map_path}: missing"]
    rows, duplicates = map_rows(map_path)
    failures.extend(duplicates)
    tests_root = root / "tests" / "formalization_lean"
    tags, misplaced = tagged_tests(tests_root)
    failures.extend(misplaced)

    decls = library_decls(root / "lean")
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
