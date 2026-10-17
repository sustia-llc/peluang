#!/usr/bin/env python3
"""Audit the axioms of every constant defined in the `Peluang` library.

Elaborates a probe that imports `Peluang` and, for every constant whose module
is `Peluang` or `Peluang.*` (theorems, definitions, instances, private and
auxiliary declarations alike), prints the axioms `Lean.collectAxioms` reports.
The probe runs as `lake env lean` with lean/ as the working directory, so elan
selects the toolchain in lean/lean-toolchain. Exit 0 when the probe
elaborates, every constant depends only on axioms in ALLOWED, every file under
lean/Peluang/ is among the loaded modules, and every theorem name scanned by
check_theorem_map is a constant of the library; exit 1 otherwise, printing
each failure on its own line. Requires a built `lake build`.

Usage: print_axioms.py [REPO_ROOT]
"""

from __future__ import annotations

import subprocess
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_theorem_map as ctm  # noqa: E402

ALLOWED = frozenset({"propext", "Classical.choice", "Quot.sound"})
TIMEOUT_S = 900
PRIVATE_PREFIX = "_private."

PROBE = """import Lean.Util.CollectAxioms
import Peluang

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames
  for m in mods do
    if (`Peluang).isPrefixOf m then
      IO.println s!"MODULE\\t{m}"
  for (n, _) in env.constants.map₁.toList do
    if let some idx := env.getModuleIdxFor? n then
      let m := mods[idx.toNat]!
      if (`Peluang).isPrefixOf m then
        let axs ← liftCoreM (Lean.collectAxioms n)
        IO.println s!"AXIOMS\\t{n}\\t{String.intercalate "," (axs.toList.map toString)}"
"""


@dataclass
class ProbeResult:
    modules: set[str] = field(default_factory=set)
    axioms: dict[str, list[str]] = field(default_factory=dict)


def display_name(name: str) -> str:
    if name.startswith(PRIVATE_PREFIX) and ".0." in name:
        return name.split(".0.", 1)[1]
    return name


def parse_output(output: str) -> ProbeResult:
    result = ProbeResult()
    for line in output.splitlines():
        parts = line.split("\t")
        if parts[0] == "MODULE" and len(parts) == 2:
            result.modules.add(parts[1])
        elif parts[0] == "AXIOMS" and len(parts) == 3:
            result.axioms[parts[1]] = [a for a in parts[2].split(",") if a]
    return result


def module_names(lean_dir: Path) -> list[str]:
    lib = lean_dir / "Peluang"
    files = sorted(lib.rglob("*.lean")) if lib.is_dir() else []
    return [".".join(p.relative_to(lean_dir).with_suffix("").parts) for p in files]


def evaluate(result: ProbeResult, on_disk: list[str], scanned: list[str]) -> list[str]:
    failures: list[str] = []
    for m in on_disk:
        if m not in result.modules:
            failures.append(f"`{m}`: file under lean/Peluang/ is not imported (transitively) by lean/Peluang.lean")
    for name, axioms in sorted(result.axioms.items()):
        bad = sorted(a for a in axioms if a not in ALLOWED)
        if bad:
            failures.append(
                f"`{display_name(name)}`: depends on {', '.join(bad)} (allowed: {', '.join(sorted(ALLOWED))})"
            )
    constants = {display_name(n) for n in result.axioms}
    for n in scanned:
        if n not in constants:
            failures.append(f"`{n}`: scanned as a theorem by check_theorem_map but is not a constant of the library")
    return failures


def check(root: Path) -> tuple[int, list[str]]:
    lean_dir = root / "lean"
    on_disk = module_names(lean_dir)
    if not on_disk:
        return 0, []
    lib = lean_dir / "Peluang"
    scanned = [d.qualified for d in ctm.lean_decls(lib)]
    with tempfile.TemporaryDirectory() as tmp:
        probe = Path(tmp) / "Probe.lean"
        probe.write_text(PROBE, encoding="utf-8")
        try:
            proc = subprocess.run(
                ["lake", "env", "lean", str(probe)],
                cwd=lean_dir,
                capture_output=True,
                text=True,
                check=False,
                timeout=TIMEOUT_S,
            )
        except (OSError, subprocess.TimeoutExpired) as e:
            return 0, [f"could not run `lake env lean` in {lean_dir}: {e}"]
    output = proc.stdout + proc.stderr
    if proc.returncode != 0:
        return 0, [f"lean exited {proc.returncode}:\n{output.rstrip()}"]
    result = parse_output(output)
    return len(result.axioms), evaluate(result, on_disk, scanned)


def main(argv: list[str]) -> int:
    root = Path(argv[1]).resolve() if len(argv) > 1 else Path(__file__).resolve().parent.parent
    count, failures = check(root)
    for f in failures:
        print(f)
    if failures:
        print(f"print_axioms: {len(failures)} failure(s) over {count} constant(s)")
        return 1
    print(f"print_axioms: ok ({count} constant(s))")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
