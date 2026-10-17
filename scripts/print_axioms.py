#!/usr/bin/env python3
"""Run `#print axioms` over every `theorem`/`lemma` under lean/Peluang/.

The probe is a `module` that does `import all` of `Peluang` and of every file
under lean/Peluang/, so private and non-public declarations resolve; it runs
as `lake env lean` with lean/ as the working directory, so elan selects the
toolchain in lean/lean-toolchain. Exit 0 when Lean elaborates the probe and
every declaration depends only on axioms in ALLOWED; exit 1 otherwise,
printing each failure on its own line. Requires a built `lake build`.

Usage: print_axioms.py [REPO_ROOT]
"""

from __future__ import annotations

import re
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_theorem_map as ctm  # noqa: E402

ALLOWED = frozenset({"propext", "Classical.choice", "Quot.sound"})
DEPENDS_RE = re.compile(r"^'(?P<name>.+?)' depends on axioms: \[(?P<axioms>[^\]]*)\]", re.M)
NONE_RE = re.compile(r"^'(?P<name>.+?)' does not depend on any axioms", re.M)
PRIVATE_RE = re.compile(r"^_private\.[\w.']*?\.0\.")


def module_names(lean_dir: Path) -> list[str]:
    lib = lean_dir / "Peluang"
    files = sorted(lib.rglob("*.lean")) if lib.is_dir() else []
    return ["Peluang", *(".".join(p.relative_to(lean_dir).with_suffix("").parts) for p in files)]


def probe_source(modules: list[str], names: list[str]) -> str:
    imports = "".join(f"import all {m}\n" for m in modules)
    return "module\n\n" + imports + "\n" + "".join(f"#print axioms {n}\n" for n in names)


def parse_output(names: list[str], output: str) -> list[str]:
    seen: dict[str, list[str]] = {}
    for m in DEPENDS_RE.finditer(output):
        seen[PRIVATE_RE.sub("", m.group("name"))] = [a.strip() for a in m.group("axioms").split(",") if a.strip()]
    for m in NONE_RE.finditer(output):
        seen[PRIVATE_RE.sub("", m.group("name"))] = []
    failures: list[str] = []
    for n in names:
        if n not in seen:
            failures.append(f"`{n}`: no `#print axioms` result")
            continue
        bad = sorted(a for a in seen[n] if a not in ALLOWED)
        if bad:
            failures.append(f"`{n}`: depends on {', '.join(bad)} (allowed: {', '.join(sorted(ALLOWED))})")
    return failures


def evaluate(names: list[str], returncode: int, output: str) -> list[str]:
    if returncode != 0:
        return [f"lean exited {returncode}:\n{output.rstrip()}"]
    return parse_output(names, output)


def check(root: Path) -> tuple[int, list[str]]:
    lean_dir = root / "lean"
    lib = lean_dir / "Peluang"
    names = [d.qualified for d in ctm.lean_decls(lib)] if lib.is_dir() else []
    with tempfile.TemporaryDirectory() as tmp:
        probe = Path(tmp) / "Probe.lean"
        probe.write_text(probe_source(module_names(lean_dir), names), encoding="utf-8")
        try:
            proc = subprocess.run(
                ["lake", "env", "lean", str(probe)],
                cwd=lean_dir,
                capture_output=True,
                text=True,
                check=False,
            )
        except OSError as e:
            return len(names), [f"could not run `lake env lean` in {lean_dir}: {e}"]
    return len(names), evaluate(names, proc.returncode, proc.stdout + proc.stderr)


def main(argv: list[str]) -> int:
    root = Path(argv[1]).resolve() if len(argv) > 1 else Path(__file__).resolve().parent.parent
    count, failures = check(root)
    for f in failures:
        print(f)
    if failures:
        print(f"print_axioms: {len(failures)} failure(s) over {count} declaration(s)")
        return 1
    print(f"print_axioms: ok ({count} declaration(s))")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
