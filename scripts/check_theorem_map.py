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
no attribute line in between is `#[ignore]` or `#[should_panic]`; and when no
line of a `.rs` file under tests/formalization_lean/, comments included,
contains the text `f64-prob` or the text `cfg` at the start of a word (which
covers `cfg_attr`); and when THEOREM_MAP.md has a `| Lean id` header line and
every later line starting with `|` is a separator or a row of three cells; and
when Cargo.toml exists and is valid TOML, and every file under
tests/formalization_lean/ holding a tag line is in the module tree of a test
target, and no target whose module tree holds such a file comes from a
`[[test]]` table with a non-empty `required-features`, `test = false` or
`harness = false`, and, under `autotests = false`, some `[[test]]` table's
module tree holds such a file. The test targets are the `[[test]]` tables,
whose root file is the table's `path`, else `tests/<name>.rs` when it exists,
else `tests/<name>/main.rs`, and, unless `autotests = false`, each
`tests/<name>.rs` and `tests/<name>/main.rs` that no table names. A module
tree follows the unindented `mod x;` declarations from the root: to `x.rs`,
else `x/mod.rs`, under the directory of the declaring file when it is the
root, a `mod.rs` or a file loaded through `#[path]`, and under `foo/` for any
other `foo.rs`; with a `#[path = "p"]` attribute above the declaration, to
`p` under the directory of the declaring file. Exit 1 otherwise, printing
each failure (each misplaced tag, each line holding that text once, with its
file and line and the text matched, each malformed table line with its line,
each such `[[test]]` table with its name, each unreached tagged file) on its
own line.

Usage: check_theorem_map.py [REPO_ROOT]
"""

from __future__ import annotations

import re
import sys
import tomllib
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
SEPARATOR_RE = re.compile(r"^\|(?:\s*:?-+:?\s*\|)+\s*$")
MOD_DECL_RE = re.compile(r"^(?:pub(?:\s*\([^)]*\))?\s+)?mod\s+(?:r#)?(\w+)\s*;")
PATH_ATTR_RE = re.compile(r'^\s*#\[\s*path\s*=\s*"([^"]*)"\s*\]\s*(?://.*)?$')
TEST_REF_RE = re.compile(r"^tests/formalization_lean/(?P<file>[\w/]+\.rs)::(?P<fn>\w+)$")
TAG_RE = re.compile(r"^\s*///\s*THEOREM_MAP:\s*(\S+)\s*$")
TEST_FN_RE = re.compile(
    r"^\s*(?:pub(?:\s*\([^)]*\)\s*|\s+))?(?:const\s+)?(?:async\s+)?(?:extern(?:\s+\"[^\"]*\")?\s+)?"
    r"fn\s+(\w+)\s*[<(]"
)
TEST_ATTR_RE = re.compile(r"^\s*#\[(?:test|(?:\w+::)+test(?:\(.*\))?)\]\s*(?://.*)?$")
BETWEEN_RE = re.compile(r"^\s*(?:#\[.*\]\s*(?://.*)?|//.*)?$")
NOT_RUN_RE = re.compile(r"^\s*#\[\s*(?:ignore|should_panic)\b")
FORBIDDEN_RE = re.compile(r"f64-prob|\bcfg")


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
    """The rows of the table that starts at the first `| Lean id` line, as Lean id → (test column, line), and
    the failures: each duplicate id, each line after the header starting with `|` that is neither a separator nor
    a row of three cells, and a missing `| Lean id` header."""
    rows: dict[str, tuple[str, int]] = {}
    failures: list[str] = []
    in_table = False
    for i, line in enumerate(map_path.read_text(encoding="utf-8").splitlines()):
        if line.startswith("| Lean id"):
            in_table = True
            continue
        if not in_table or not line.startswith("|"):
            continue
        if SEPARATOR_RE.match(line):
            continue
        m = ROW_RE.match(line)
        if not m:
            failures.append(f"THEOREM_MAP.md:{i + 1}: table line is not a row `| <id> | <test> | <anchor> |`")
            continue
        lean_id = m.group("id")
        if lean_id in rows:
            failures.append(f"THEOREM_MAP.md:{i + 1}: duplicate row for `{lean_id}` (first at line {rows[lean_id][1]})")
            continue
        rows[lean_id] = (m.group("test"), i + 1)
    if not in_table:
        failures.append("THEOREM_MAP.md: no `| Lean id` table header")
    return rows, failures


def tagged_tests(tests_root: Path) -> tuple[dict[str, list[tuple[Path, str]]], set[Path], list[str]]:
    """The placed tags (id → (file, fn)), the resolved files holding a tag line, and the tag-placement and
    forbidden-text failures, over the `.rs` files under `tests_root`."""
    tags: dict[str, list[tuple[Path, str]]] = {}
    tagged: set[Path] = set()
    failures: list[str] = []
    if not tests_root.is_dir():
        return tags, tagged, failures
    for path in sorted(tests_root.rglob("*.rs")):
        lines = path.read_text(encoding="utf-8").splitlines()
        for i, line in enumerate(lines):
            forbidden = list(dict.fromkeys(FORBIDDEN_RE.findall(line)))
            if forbidden:
                failures.append(f"{path}:{i + 1}: contains the text {', '.join(f'`{t}`' for t in forbidden)}")
            m = TAG_RE.match(line)
            if not m:
                continue
            tagged.add(path.resolve())
            fm = None
            blocking: list[str] = []
            if i + 1 < len(lines) and TEST_ATTR_RE.match(lines[i + 1]):
                j = i + 2
                while j < len(lines) and BETWEEN_RE.match(lines[j]) and not TAG_RE.match(lines[j]):
                    if NOT_RUN_RE.match(lines[j]):
                        blocking.append(lines[j].strip())
                    j += 1
                fm = TEST_FN_RE.match(lines[j]) if j < len(lines) else None
            if fm and blocking:
                failures.append(
                    f"{path}:{i + 1}: `/// THEOREM_MAP: {m.group(1)}` sits on a test that does not run "
                    f"or does not assert: {', '.join(f'`{b}`' for b in blocking)}"
                )
            elif fm:
                tags.setdefault(m.group(1), []).append((path, fm.group(1)))
            else:
                failures.append(
                    f"{path}:{i + 1}: `/// THEOREM_MAP: {m.group(1)}` is not on the line directly above "
                    "`#[test]` on a fn"
                )
    return tags, tagged, failures


def target_root(root: Path, table: dict[str, object]) -> Path | None:
    """The root file of a `[[test]]` table: `path`, else `tests/<name>.rs` when it exists, else `tests/<name>/main.rs`."""
    path = table.get("path")
    if isinstance(path, str):
        return (root / path).resolve()
    name = table.get("name")
    if not isinstance(name, str):
        return None
    flat = root / "tests" / f"{name}.rs"
    return (flat if flat.is_file() else root / "tests" / name / "main.rs").resolve()


@dataclass(frozen=True)
class Target:
    name: str
    root: Path
    table: dict[str, object] | None  # None for a target Cargo discovers without a `[[test]]` table


def test_targets(root: Path, manifest: dict[str, object]) -> tuple[list[Target], bool]:
    """The test targets of `manifest` and whether `autotests` is on: each `[[test]]` table with its root file, and,
    when `package.autotests` is not `false`, each `tests/<name>.rs` and `tests/<name>/main.rs` whose name and root
    no table already has."""
    targets: list[Target] = []
    tables = manifest.get("test", [])
    for table in tables if isinstance(tables, list) else []:
        if not isinstance(table, dict):
            continue
        target = target_root(root, table)
        if target is not None:
            targets.append(Target(str(table.get("name", target)), target, table))
    package = manifest.get("package")
    autotests = not (isinstance(package, dict) and package.get("autotests") is False)
    tests_dir = root / "tests"
    if autotests and tests_dir.is_dir():
        names = {t.name for t in targets}
        roots = {t.root for t in targets}
        for path in sorted(tests_dir.glob("*.rs")) + sorted(tests_dir.glob("*/main.rs")):
            name = path.stem if path.parent == tests_dir else path.parent.name
            if name not in names and path.resolve() not in roots:
                targets.append(Target(name, path.resolve(), None))
    return targets, autotests


def module_tree(target: Path) -> set[Path]:
    """The resolved files of the module tree rooted at the crate root `target`. A `mod x;` declaration at the start
    of a line resolves to `x.rs`, else `x/mod.rs`, under the directory of the declaring file when that file is the
    root, a `mod.rs` or a file loaded through `#[path]`, and under `foo/` for any other file `foo.rs`. A
    `#[path = "p"]` attribute on the lines above it (only attributes, comments and blank lines between) resolves
    it to `p` under the directory of the declaring file. An indented `mod x;` is not followed."""
    reached: set[Path] = set()
    stack: list[tuple[Path, Path]] = [(target, target.parent)]
    while stack:
        path, base = stack.pop()
        if path in reached or not path.is_file():
            continue
        reached.add(path)
        pending: str | None = None
        for line in path.read_text(encoding="utf-8").splitlines():
            pm = PATH_ATTR_RE.match(line)
            if pm:
                pending = pm.group(1)
                continue
            m = MOD_DECL_RE.match(line)
            if m:
                if pending is not None:
                    child = (path.parent / pending).resolve()
                    stack.append((child, child.parent))
                else:
                    flat = base / f"{m.group(1)}.rs"
                    child = (flat if flat.is_file() else base / m.group(1) / "mod.rs").resolve()
                    stack.append((child, child.parent if child.name == "mod.rs" else child.with_suffix("")))
                pending = None
            elif not BETWEEN_RE.match(line):
                pending = None
    return reached


def witness_target_failures(root: Path, tagged: set[Path]) -> list[str]:
    """Failures of the test targets over the resolved files `tagged` holding a THEOREM_MAP tag: a missing or invalid
    Cargo.toml; a target whose module tree holds a tagged file and that has a non-empty `required-features`,
    `test = false` or `harness = false`; `autotests = false` with no `[[test]]` table whose tree holds a tagged
    file; each tagged file that no target's module tree holds."""
    cargo = root / "Cargo.toml"
    if not cargo.is_file():
        return [f"{cargo}: missing"]
    try:
        manifest = tomllib.loads(cargo.read_text(encoding="utf-8"))
    except tomllib.TOMLDecodeError as error:
        return [f"{cargo}: not valid TOML: {error}"]
    failures: list[str] = []
    targets, autotests = test_targets(root, manifest)
    reached: set[Path] = set()
    table_holds = False
    for t in targets:
        held = module_tree(t.root) & tagged
        if not held:
            continue
        reached |= held
        if t.table is None:
            continue
        table_holds = True
        features = t.table.get("required-features")
        if features:
            failures.append(
                f"{cargo}: [[test]] `{t.name}` holds THEOREM_MAP witnesses and has required-features {features}"
            )
        for key in ("test", "harness"):
            if t.table.get(key) is False:
                failures.append(f"{cargo}: [[test]] `{t.name}` holds THEOREM_MAP witnesses and has {key} = false")
    if tagged and not autotests and not table_holds:
        failures.append(f"{cargo}: autotests = false and no [[test]] table holds the THEOREM_MAP witnesses")
    for path in sorted(tagged - reached):
        failures.append(f"{path}: holds a THEOREM_MAP tag and no mod declaration from a test target root reaches it")
    return failures


def check(root: Path) -> list[str]:
    failures: list[str] = []
    map_path = root / "THEOREM_MAP.md"
    if not map_path.is_file():
        return [f"{map_path}: missing"]
    rows, row_failures = map_rows(map_path)
    failures.extend(row_failures)
    tags, tagged, test_failures = tagged_tests(root / "tests" / "formalization_lean")
    failures.extend(test_failures)
    failures.extend(witness_target_failures(root, tagged))

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
