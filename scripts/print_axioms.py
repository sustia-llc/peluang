#!/usr/bin/env python3
"""Run `#print axioms` over every `theorem`/`lemma` under lean/Peluang/.

Exit 0 when Lean elaborates the probe file and every declaration depends only
on axioms in ALLOWED; exit 1 otherwise, printing each failure on its own line.
A declaration with no `#print axioms` result from `import Peluang` is a
failure. Requires a built `lake -d lean build`.

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
DEPENDS_RE = re.compile(r"^'(?P<name>[^']+)' depends on axioms: \[(?P<axioms>[^\]]*)\]\s*$")
NONE_RE = re.compile(r"^'(?P<name>[^']+)' does not depend on any axioms\s*$")


def probe_source(names: list[str]) -> str:
    return "import Peluang\n\n" + "".join(f"#print axioms {n}\n" for n in names)


def parse_output(names: list[str], output: str) -> list[str]:
    seen: dict[str, list[str]] = {}
    for line in output.splitlines():
        m = DEPENDS_RE.match(line)
        if m:
            seen[m.group("name")] = [a.strip() for a in m.group("axioms").split(",") if a.strip()]
            continue
        m = NONE_RE.match(line)
        if m:
            seen[m.group("name")] = []
    failures: list[str] = []
    for n in names:
        if n not in seen:
            failures.append(f"`{n}`: no `#print axioms` result")
            continue
        bad = sorted(a for a in seen[n] if a not in ALLOWED)
        if bad:
            failures.append(f"`{n}`: depends on {', '.join(bad)} (allowed: {', '.join(sorted(ALLOWED))})")
    return failures


def check(root: Path) -> tuple[int, list[str]]:
    lean_dir = root / "lean"
    lib = lean_dir / "Peluang"
    names = [d.qualified for d in ctm.lean_decls(lib)] if lib.is_dir() else []
    with tempfile.TemporaryDirectory() as tmp:
        probe = Path(tmp) / "Probe.lean"
        probe.write_text(probe_source(names), encoding="utf-8")
        proc = subprocess.run(
            ["lake", "-d", str(lean_dir), "env", "lean", str(probe)],
            capture_output=True,
            text=True,
            check=False,
        )
    output = proc.stdout + proc.stderr
    failures = parse_output(names, output)
    if proc.returncode != 0:
        failures.insert(0, f"lean exited {proc.returncode}:\n{output.rstrip()}")
    return len(names), failures


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
