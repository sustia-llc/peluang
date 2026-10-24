#!/usr/bin/env python3
"""Check through Lean that the `PeluangTest` library holds only `example`s.

Requires an up-to-date build of the `PeluangTest` target (checked with
`lake build --no-build PeluangTest`). The test modules are lean/PeluangTest.lean
and every `*.lean` file under lean/PeluangTest/. The import check runs
scripts/lean/ImportCheck.lean once over all of them: every loaded module named
`PeluangTest` or `PeluangTest.*` has no `constNames`, no `extraConstNames` and
no non-empty extension entries outside ALLOWED_EXTENSIONS, and every test module
is loaded. The example check runs scripts/lean/ExampleCheck.lean once per test
module, under the `leanOptions` of lean/lakefile.lean, which must hold exactly
one `leanOptions := #[…]` block outside comments, every entry of it a
⟨`name, value⟩ with a Bool, Nat or String literal value, and no
`moreLeanArgs`, `weakLeanArgs`, `moreServerOptions` or `moreServerArgs`
outside comments: no constant survives
in the file's environment, every constant seen only in a command's info tree
depends on axioms in ALLOWED only, re-elaboration reports no error, and the
number of hidden `_example` constants equals the number of `example` commands.
The plant check runs the example check on a temporary file outside the repo
holding an `example` proved by `native_decide`, and requires a zero exit and
its `_native.native_decide.ax_*` axiom to be reported. The declaration plant
check compiles a temporary file outside the repo holding one `theorem`, and
requires the import check to report it as a constant and the example check to
report it as a surviving constant. Every `lake` call runs with
lean/ as the working directory. Exit 0 when every check passes; exit 1
otherwise, printing each failure on its own line.

Usage: check_peluangtest.py [REPO_ROOT]
"""

from __future__ import annotations

import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_lean_source import strip_code  # noqa: E402
from check_theorem_map import library_files  # noqa: E402
from print_axioms import ALLOWED, display_name, module_names, run_lake  # noqa: E402

TEST_ROOT = "PeluangTest"
ALLOWED_EXTENSIONS = frozenset(
    {
        "_private.Lean.DocString.Extension.0.Lean.moduleDocExt",
        "_private.Lean.Compiler.ModPkgExt.0.Lean.modPkgExt",
        "_private.Lean.ExtraModUses.0.Lean.extraModUses",
        "Lean.deprecatedModuleExt",
    }
)
EXAMPLE_NAME = "_example"
PLANT_AXIOM = "._native.native_decide.ax_"
PLANT_MODULE = "PeluangTestPlant"
PLANT = """module

example : 2 + 2 = 4 := by native_decide
"""
DECL_PLANT_MODULE = "PeluangTestDeclPlant"
DECL_PLANT_CONST = "peluangTestDeclPlant"
DECL_PLANT = f"theorem {DECL_PLANT_CONST} : True := trivial\n"
ESCAPES = {"n": "\n", "t": "\t", "r": "\r"}
LEAN_OPTIONS_RE = re.compile(r"leanOptions\s*:=\s*#\[(?P<body>[^\]]*)\]")
ENTRY_RE = re.compile(r"⟨")
OTHER_OPTIONS_RE = re.compile(r"\b(?:moreLeanArgs|moreServerOptions|weakLeanArgs|moreServerArgs)\b")
OPTION_RE = re.compile(r"⟨\s*`(?P<name>[\w.]+)\s*,\s*(?P<value>true|false|\d+|\"[^\"]*\")\s*⟩")


@dataclass
class ImportReport:
    modules: set[str] = field(default_factory=set)
    consts: list[tuple[str, str]] = field(default_factory=list)
    extras: list[tuple[str, str]] = field(default_factory=list)
    entries: list[tuple[str, str, int]] = field(default_factory=list)
    done: bool = False


@dataclass(frozen=True)
class Hidden:
    line: int
    name: str
    axioms: tuple[str, ...]


@dataclass
class ExampleReport:
    finals: list[tuple[str, tuple[str, ...]]] = field(default_factory=list)
    hidden: list[Hidden] = field(default_factory=list)
    examples: int | None = None
    messages: list[tuple[str, int, str]] = field(default_factory=list)
    done: bool = False


def axioms_of(field_text: str) -> tuple[str, ...]:
    return tuple(a for a in field_text.split(",") if a)


def last_component(name: str) -> str:
    return display_name(name).rsplit(".", 1)[-1]


def unescape(text: str) -> str:
    return re.sub(r"\\(.)", lambda m: ESCAPES.get(m.group(1), m.group(1)), text)


def parse_import_output(output: str) -> ImportReport:
    r = ImportReport()
    for line in output.split("\n"):
        parts = line.split("\t")
        if parts[0] == "MODULE" and len(parts) == 2:
            r.modules.add(parts[1])
        elif parts[0] == "CONST" and len(parts) == 3:
            r.consts.append((parts[1], parts[2]))
        elif parts[0] == "EXTRA" and len(parts) == 3:
            r.extras.append((parts[1], parts[2]))
        elif parts[0] == "ENTRIES" and len(parts) == 4 and parts[3].isdigit():
            r.entries.append((parts[1], parts[2], int(parts[3])))
        elif parts == ["DONE"]:
            r.done = True
    return r


def parse_example_output(output: str) -> ExampleReport:
    r = ExampleReport()
    for line in output.split("\n"):
        parts = line.split("\t")
        if parts[0] == "FINAL" and len(parts) == 4:
            r.finals.append((parts[2], axioms_of(parts[3])))
        elif parts[0] == "HIDDEN" and len(parts) == 5 and parts[2].isdigit():
            r.hidden.append(Hidden(int(parts[2]), parts[3], axioms_of(parts[4])))
        elif parts[0] == "EXAMPLES" and len(parts) == 3 and parts[2].isdigit():
            r.examples = int(parts[2])
        elif parts[0] == "MSG" and len(parts) == 5 and parts[3].isdigit():
            r.messages.append((parts[2], int(parts[3]), unescape(parts[4])))
        elif parts[0] == "DONE" and len(parts) == 2:
            r.done = True
    return r


def hidden_examples(r: ExampleReport) -> int:
    return sum(1 for h in r.hidden if last_component(h.name) == EXAMPLE_NAME)


def lean_options(lakefile_text: str) -> list[str] | None:
    code = strip_code(lakefile_text)
    found = list(LEAN_OPTIONS_RE.finditer(code))
    if len(found) != 1 or OTHER_OPTIONS_RE.search(code):
        return None
    start, end = found[0].span("body")
    parsed = list(OPTION_RE.finditer(lakefile_text[start:end]))
    if len(parsed) != len(ENTRY_RE.findall(code[start:end])):
        return None
    return [f"{o['name']}={o['value'].strip(chr(34))}" for o in parsed]


def evaluate_imports(r: ImportReport, modules: list[str]) -> list[str]:
    failures: list[str] = []
    if not r.done:
        failures.append("import check: output ended before DONE")
    for m in modules:
        if m not in r.modules:
            failures.append(f"`{m}`: not loaded by the import check")
    for m, n in r.consts:
        failures.append(f"`{m}`: defines constant `{display_name(n)}` ({n})")
    for m, n in r.extras:
        failures.append(f"`{m}`: defines extra constant `{display_name(n)}` ({n})")
    for m, ext, count in r.entries:
        if ext not in ALLOWED_EXTENSIONS:
            failures.append(f"`{m}`: adds {count} entr{'y' if count == 1 else 'ies'} to extension `{ext}`")
    return failures


def evaluate_examples(r: ExampleReport, label: str) -> list[str]:
    failures: list[str] = []
    if not r.done:
        failures.append(f"{label}: example check output ended before DONE")
    for n, axs in r.finals:
        failures.append(f"{label}: constant `{display_name(n)}` survives in the file's environment ({', '.join(axs) or 'no axioms'})")
    for h in r.hidden:
        bad = sorted(a for a in h.axioms if a not in ALLOWED)
        if bad:
            failures.append(
                f"{label}:{h.line}: `{display_name(h.name)}` depends on {', '.join(bad)} "
                f"(allowed: {', '.join(sorted(ALLOWED))})"
            )
    for severity, line, text in r.messages:
        if severity == "error":
            failures.append(f"{label}:{line}: error: {text}")
    found = hidden_examples(r)
    if r.examples is None:
        failures.append(f"{label}: example check printed no EXAMPLES row")
    elif found != r.examples:
        failures.append(f"{label}: {found} hidden `{EXAMPLE_NAME}` constant(s) for {r.examples} `example` command(s)")
    return failures


def plant_reported(r: ExampleReport) -> bool:
    return any(PLANT_AXIOM in a and a not in ALLOWED for h in r.hidden for a in h.axioms)


def run_import_check(
    lean_dir: Path, script_dir: Path, prefix: str, modules: list[str], env: dict[str, str] | None = None
) -> tuple[subprocess.CompletedProcess[str], ImportReport]:
    proc = run_lake(["env", "lean", "--run", str(script_dir / "ImportCheck.lean"), prefix, *modules], lean_dir, env)
    return proc, parse_import_output(proc.stdout)


def run_example_check(
    lean_dir: Path, script_dir: Path, path: Path, module: str, options: list[str]
) -> tuple[subprocess.CompletedProcess[str], ExampleReport]:
    proc = run_lake(["env", "lean", "--run", str(script_dir / "ExampleCheck.lean"), str(path), module, *options], lean_dir)
    return proc, parse_example_output(proc.stdout)


def exit_failure(proc: subprocess.CompletedProcess[str], label: str) -> list[str]:
    if proc.returncode == 0:
        return []
    return [f"{label}: lean exited {proc.returncode}:\n{(proc.stdout + proc.stderr).rstrip()}"]


@dataclass
class Summary:
    examples: dict[str, int] = field(default_factory=dict)
    constants: int = 0
    plant: bool = False
    decl_plant: bool = False
    failures: list[str] = field(default_factory=list)


def decl_plant_reported(imports: ImportReport, report: ExampleReport) -> bool:
    imported = any(display_name(n) == DECL_PLANT_CONST for _, n in imports.consts)
    final = any(display_name(n) == DECL_PLANT_CONST for n, _ in report.finals)
    return imported and final


def run_decl_plant(lean_dir: Path, script_dir: Path, options: list[str]) -> tuple[bool, str]:
    with tempfile.TemporaryDirectory() as tmp:
        src, olean_dir = Path(tmp) / "src", Path(tmp) / "out"
        src.mkdir()
        olean_dir.mkdir()
        plant = src / f"{DECL_PLANT_MODULE}.lean"
        plant.write_text(DECL_PLANT, encoding="utf-8")
        built = run_lake(["env", "lean", "-R", str(src), "-o", str(olean_dir / f"{DECL_PLANT_MODULE}.olean"), str(plant)], lean_dir)
        if built.returncode != 0:
            return False, (built.stdout + built.stderr).rstrip()
        iproc, imports = run_import_check(lean_dir, script_dir, DECL_PLANT_MODULE, [DECL_PLANT_MODULE], {"LEAN_PATH": str(olean_dir)})
        eproc, report = run_example_check(lean_dir, script_dir, plant, DECL_PLANT_MODULE, options)
    ok = iproc.returncode == 0 and eproc.returncode == 0 and decl_plant_reported(imports, report)
    return ok, (iproc.stdout + iproc.stderr + eproc.stdout + eproc.stderr).rstrip()


def check(root: Path) -> Summary:
    lean_dir = root / "lean"
    script_dir = Path(__file__).resolve().parent / "lean"
    out = Summary()
    files = library_files(lean_dir, TEST_ROOT)
    if not files:
        out.failures.append(f"no test modules under {lean_dir}")
        return out
    modules = module_names(lean_dir, TEST_ROOT)
    failures = out.failures
    try:
        lakefile = lean_dir / "lakefile.lean"
        options = lean_options(lakefile.read_text(encoding="utf-8"))
        if options is None:
            failures.append(
                f"{lakefile}: expected exactly one `leanOptions := #[…]` block, each entry ⟨`name, value⟩ "
                "with a Bool, Nat or String literal value, and no moreLeanArgs, weakLeanArgs, moreServerOptions "
                "or moreServerArgs"
            )
            return out
        fresh = run_lake(["build", "--no-build", TEST_ROOT], lean_dir)
        if fresh.returncode != 0:
            failures.append(
                f"lean build is stale or missing; run `env -C lean lake build {TEST_ROOT}`:\n{(fresh.stdout + fresh.stderr).rstrip()}"
            )
            return out
        proc, imports = run_import_check(lean_dir, script_dir, TEST_ROOT, modules)
        failures += exit_failure(proc, "import check")
        failures += evaluate_imports(imports, modules)
        out.constants += len(imports.consts) + len(imports.extras)
        for path, module in zip(files, modules):
            label = str(path.relative_to(root))
            proc, report = run_example_check(lean_dir, script_dir, path, module, options)
            failures += exit_failure(proc, label)
            failures += evaluate_examples(report, label)
            out.examples[label] = report.examples or 0
        with tempfile.TemporaryDirectory() as tmp:
            plant = Path(tmp) / f"{PLANT_MODULE}.lean"
            plant.write_text(PLANT, encoding="utf-8")
            proc, report = run_example_check(lean_dir, script_dir, plant, PLANT_MODULE, options)
        out.plant = proc.returncode == 0 and plant_reported(report)
        if not out.plant:
            failures.append(
                f"plant: the `native_decide` example was not reported (example check output:\n{(proc.stdout + proc.stderr).rstrip()})"
            )
        out.decl_plant, output = run_decl_plant(lean_dir, script_dir, options)
        if not out.decl_plant:
            failures.append(
                f"declaration plant: `{DECL_PLANT_CONST}` was not reported by both the import and the example check "
                f"(output:\n{output})"
            )
    except (OSError, subprocess.TimeoutExpired) as e:
        failures.append(f"could not run `lake` in {lean_dir}: {e}")
    return out


def count_line(s: Summary) -> str:
    per_file = ", ".join(f"{k} {v}" for k, v in s.examples.items())
    return (
        f"check_peluangtest: {len(s.examples)} file(s), {sum(s.examples.values())} example(s), "
        f"{s.constants} constant(s), plant {'reported' if s.plant else 'not reported'}, "
        f"declaration plant {'reported' if s.decl_plant else 'not reported'} ({per_file})"
    )


def main(argv: list[str]) -> int:
    root = Path(argv[1]).resolve() if len(argv) > 1 else Path(__file__).resolve().parent.parent
    s = check(root)
    for f in s.failures:
        print(f)
    if s.failures:
        print(f"check_peluangtest: {len(s.failures)} failure(s) over {len(s.examples)} file(s)")
        return 1
    print("check_peluangtest: ok")
    print(count_line(s))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
