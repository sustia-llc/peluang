#!/usr/bin/env python3
"""End-to-end self-test of print_axioms.py against a planted Lean module.

Writes lean/Peluang/ProbeSelfTest.lean (constants built with `sorry` and
`native_decide`, plus a clean theorem), imports it from lean/Peluang.lean,
runs `lake build` and print_axioms.check, then restores both files. Exit 0
when the probe reports a disallowed-axiom failure for exactly the planted
constants and nothing else; exit 1 otherwise. Requires the Mathlib cache.

Usage: probe_selftest.py [REPO_ROOT]
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import print_axioms as pa  # noqa: E402

FIXTURE = """module

public import Mathlib.CategoryTheory.MarkovCategory.Basic

namespace Peluang.ProbeSelfTest

theorem outsideSorry : (1 : Nat) = 2 := sorry

private theorem privSorry : (3 : Nat) = 4 := sorry

def defSorry : Nat := sorry

end Peluang.ProbeSelfTest

public section

namespace Peluang.ProbeSelfTest

structure Box where
  n : Nat

instance : Inhabited Box := ⟨⟨sorry⟩⟩

theorem pubSorry : (5 : Nat) = 6 := sorry

theorem nativeThm : (10 : Nat) < 11 := by native_decide

theorem clean (p : Prop) : p ∨ ¬p := Classical.em p

end Peluang.ProbeSelfTest

end
"""
IMPORT = "public import Peluang.ProbeSelfTest\n"
PLANTED = {
    "Peluang.ProbeSelfTest.outsideSorry",
    "Peluang.ProbeSelfTest.privSorry",
    "Peluang.ProbeSelfTest.defSorry",
    "Peluang.ProbeSelfTest.instInhabitedBox",
    "Peluang.ProbeSelfTest.pubSorry",
    "Peluang.ProbeSelfTest.nativeThm",
}


def with_import(root_src: str) -> str:
    lines = root_src.splitlines(keepends=True)
    last = max(i for i, line in enumerate(lines) if line.startswith("public import "))
    return "".join([*lines[: last + 1], IMPORT, *lines[last + 1 :]])


def flagged(failures: list[str]) -> set[str]:
    names = set()
    for f in failures:
        if ": depends on " in f and f.startswith("`"):
            name = f[1 : f.index("`", 1)]
            if not name.startswith("_"):
                names.add(name.split("._native.")[0])
    return names


def run(root: Path) -> list[str]:
    lean_dir = root / "lean"
    root_file = lean_dir / "Peluang.lean"
    fixture = lean_dir / "Peluang" / "ProbeSelfTest.lean"
    original = root_file.read_text(encoding="utf-8")
    created_dir = not fixture.parent.exists()
    try:
        fixture.parent.mkdir(exist_ok=True)
        fixture.write_text(FIXTURE, encoding="utf-8")
        root_file.write_text(with_import(original), encoding="utf-8")
        build = subprocess.run(["lake", "build"], cwd=lean_dir, capture_output=True, text=True, check=False)
        if build.returncode != 0:
            return [f"lake build of the fixture failed ({build.returncode}):\n{(build.stdout + build.stderr).rstrip()}"]
        _, failures = pa.check(root)
    finally:
        root_file.write_text(original, encoding="utf-8")
        fixture.unlink(missing_ok=True)
        if created_dir:
            fixture.parent.rmdir()
    problems: list[str] = []
    got = flagged(failures)
    for name in sorted(PLANTED - got):
        problems.append(f"`{name}`: planted but not reported by print_axioms")
    for name in sorted(got - PLANTED):
        problems.append(f"`{name}`: reported by print_axioms but not planted")
    others = [f for f in failures if ": depends on " not in f]
    problems.extend(f"unexpected print_axioms failure: {f}" for f in others)
    return problems


def main(argv: list[str]) -> int:
    root = Path(argv[1]).resolve() if len(argv) > 1 else Path(__file__).resolve().parent.parent
    problems = run(root)
    for p in problems:
        print(p)
    if problems:
        print(f"probe_selftest: {len(problems)} problem(s)")
        return 1
    print(f"probe_selftest: ok ({len(PLANTED)} planted constants reported)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
