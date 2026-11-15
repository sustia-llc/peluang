#!/usr/bin/env python3
"""Unit tests for print_axioms (no Lean needed)."""

from __future__ import annotations

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import print_axioms as pa  # noqa: E402

SOURCE = """namespace Peluang
@[reassoc]
theorem compId : True := trivial
theorem «odd name» : True := trivial
instance : Nonempty Nat := ⟨0⟩
alias plainAlias := compId
/-- theorem in a docstring -/
def d : Nat := 0
end Peluang
""".splitlines()


def const(name: str, ranges: tuple[int, int, int, int, int, int] | None, theorem: bool = True, axioms: tuple[str, ...] = ()) -> pa.Const:
    return pa.Const(name, "Peluang", theorem, ranges, axioms)


ALLOWED_ROW = "ALLOWED\tQuot.sound,Classical.choice,propext"


def probe(*lines: str, allowed: bool = True) -> pa.ProbeResult:
    return pa.parse_output("".join(f"{line}\n" for line in ((ALLOWED_ROW,) if allowed else ()) + lines))


class ParseOutput(unittest.TestCase):
    def test_modules_and_consts(self) -> None:
        r = probe(
            "MODULE\tPeluang",
            "CONST\tPeluang.a\tPeluang\ttrue\t2:0:3:8:3:14\tpropext,Quot.sound",
            "CONST\tPeluang.Box.mk.inj\tPeluang\ttrue\t-\t",
        )
        self.assertEqual(r.modules, {"Peluang"})
        self.assertEqual(r.consts[0], pa.Const("Peluang.a", "Peluang", True, (2, 0, 3, 8, 3, 14), ("propext", "Quot.sound")))
        self.assertEqual(r.consts[1].ranges, None)

    def test_unrelated_lines_ignored(self) -> None:
        r = pa.parse_output("warning: something\nCONST\ttoo\tfew\n")
        self.assertEqual((r.modules, r.consts, r.allowed), (set(), [], None))

    def test_allowed_row(self) -> None:
        self.assertEqual(probe().allowed, frozenset({"propext", "Classical.choice", "Quot.sound"}))


class SourceTheorem(unittest.TestCase):
    def test_theorem_with_attribute_above_is_source(self) -> None:
        self.assertTrue(pa.is_source_theorem(const("Peluang.compId", (2, 0, 3, 8, 3, 14)), SOURCE))

    def test_guillemet_theorem_is_source(self) -> None:
        self.assertTrue(pa.is_source_theorem(const("Peluang.«odd name»", (4, 0, 4, 8, 4, 18)), SOURCE))

    def test_attribute_generated_lemma_is_not_source(self) -> None:
        self.assertFalse(pa.is_source_theorem(const("Peluang.compId_assoc", (2, 2, 2, 2, 2, 9)), SOURCE))

    def test_prop_instance_is_not_source(self) -> None:
        self.assertFalse(pa.is_source_theorem(const("Peluang.instNonemptyNat", (5, 0, 5, 0, 5, 8)), SOURCE))

    def test_alias_is_not_source(self) -> None:
        self.assertFalse(pa.is_source_theorem(const("Peluang.plainAlias", (6, 0, 6, 6, 6, 16)), SOURCE))

    def test_keyword_inside_docstring_does_not_count(self) -> None:
        self.assertFalse(pa.is_source_theorem(const("Peluang.d", (7, 0, 8, 4, 8, 5)), SOURCE))

    def test_no_ranges_or_not_theorem_is_not_source(self) -> None:
        self.assertFalse(pa.is_source_theorem(const("Peluang.compId", None), SOURCE))
        self.assertFalse(pa.is_source_theorem(const("Peluang.compId", (2, 0, 3, 8, 3, 14), theorem=False), SOURCE))


class Evaluate(unittest.TestCase):
    def test_disallowed_axiom_fails_with_display_name(self) -> None:
        r = probe("MODULE\tPeluang", "CONST\t_private.Peluang.0.Peluang.h\tPeluang\ttrue\t-\tsorryAx")
        failures = pa.evaluate(r, ["Peluang"], [], set())
        self.assertEqual(failures, ["`Peluang.h`: depends on sorryAx (allowed: Classical.choice, Quot.sound, propext)"])

    def test_native_decide_axiom_fails(self) -> None:
        r = probe("MODULE\tPeluang", "CONST\tPeluang.d\tPeluang\tfalse\t-\tPeluang.d._native.native_decide.ax_1_1")
        failures = pa.evaluate(r, ["Peluang"], [], set())
        self.assertEqual(len(failures), 1, failures)
        self.assertIn("native_decide", failures[0])

    def test_orphan_module_fails(self) -> None:
        failures = pa.evaluate(probe("MODULE\tPeluang"), ["Peluang", "Peluang.Orphan"], [], set())
        self.assertEqual(failures, ["`Peluang.Orphan`: library file is not imported (transitively) by lean/Peluang.lean"])

    def test_scanned_name_not_a_source_theorem_fails(self) -> None:
        failures = pa.evaluate(probe("MODULE\tPeluang"), ["Peluang"], ["Peluang.a", "Peluang.ghost"], {"Peluang.a"})
        self.assertEqual(failures, ["`Peluang.ghost`: scanned as a theorem by check_theorem_map but is not a source theorem of the library"])

    def test_source_theorem_missed_by_scanner_fails(self) -> None:
        failures = pa.evaluate(probe("MODULE\tPeluang"), ["Peluang"], ["Peluang.a"], {"Peluang.a", "Peluang.missed"})
        self.assertEqual(failures, ["`Peluang.missed`: source theorem of the library that check_theorem_map does not scan"])

    def test_missing_allowed_row_fails(self) -> None:
        r = probe("MODULE\tPeluang", "CONST\tPeluang.a\tPeluang\ttrue\t-\tpropext", allowed=False)
        failures = pa.evaluate(r, ["Peluang"], ["Peluang.a"], {"Peluang.a"})
        self.assertEqual(failures[0], "probe printed no ALLOWED row (Peluang.Linter.allowedAxioms)", failures)
        self.assertEqual(len(failures), 2, failures)

    def test_empty_allowed_row_fails(self) -> None:
        r = pa.parse_output("ALLOWED\t\nMODULE\tPeluang\n")
        self.assertEqual(pa.evaluate(r, ["Peluang"], [], set()), ["Peluang.Linter.allowedAxioms is empty"])

    def test_clean_probe_passes(self) -> None:
        r = probe("MODULE\tPeluang", "MODULE\tPeluang.X", "CONST\tPeluang.a\tPeluang.X\ttrue\t-\tpropext")
        self.assertEqual(pa.evaluate(r, ["Peluang", "Peluang.X"], ["Peluang.a"], {"Peluang.a"}), [])


REPO = Path(__file__).resolve().parent.parent
NOT_A_CONSTANT = "is not a constant of a `Peluang` / `Peluang.*` module"


def lake_ok(output: str):
    def fake_run_lake(args: list[str], lean_dir: Path, env: dict[str, str] | None = None) -> subprocess.CompletedProcess[str]:
        return subprocess.CompletedProcess(["lake", *args], 0, output if args[0] == "env" else "", "")

    return fake_run_lake


class MapRows(unittest.TestCase):
    def test_stale_id_fails_with_name_and_line(self) -> None:
        r = probe("MODULE\tPeluang", "CONST\tPeluang.instCopy\tPeluang\tfalse\t-\t")
        failures = pa.unresolved_rows(r, {"Peluang.instCopy": 43, "Peluang.instCopyRenamed": 44})
        self.assertEqual(failures, [f"THEOREM_MAP.md:44: `Peluang.instCopyRenamed` {NOT_A_CONSTANT}"])

    def test_mathlib_row_is_skipped(self) -> None:
        self.assertEqual(pa.unresolved_rows(probe(), {"mathlib:CategoryTheory.MarkovCategory.eq_discard": 3}), [])

    def test_constant_outside_peluang_modules_does_not_resolve(self) -> None:
        r = probe("MODULE\tPeluangLint", "CONST\tPeluang.Linter.allowedAxioms\tPeluangLint\tfalse\t-\t")
        failures = pa.unresolved_rows(r, {"Peluang.Linter.allowedAxioms": 7})
        self.assertEqual(failures, [f"THEOREM_MAP.md:7: `Peluang.Linter.allowedAxioms` {NOT_A_CONSTANT}"])

    def test_private_constant_resolves_only_by_its_display_name(self) -> None:
        full = "_private.Peluang.X.0.Peluang.h"
        r = probe("MODULE\tPeluang.X", f"CONST\t{full}\tPeluang.X\ttrue\t-\t")
        failures = pa.unresolved_rows(r, {"Peluang.h": 9, full: 10})
        self.assertEqual(failures, [f"THEOREM_MAP.md:10: `{full}` {NOT_A_CONSTANT}"])

    def test_private_theorem_row_passes_print_axioms_and_check_theorem_map(self) -> None:
        source = "namespace Peluang\nprivate theorem h : True := trivial\nend Peluang\n"
        output = f"{ALLOWED_ROW}\nMODULE\tPeluang\nCONST\t_private.Peluang.0.Peluang.h\tPeluang\ttrue\t2:0:2:16:2:17\t\n"
        table = "| Lean id | Rust test | anchor |\n|---|---|---|\n| Peluang.h | tests/formalization_lean/a.rs::h | x |\n"
        witness = "/// THEOREM_MAP: Peluang.h\n#[test]\nfn h() {}\n"
        with mock.patch.object(pa, "run_lake", lake_ok(output)), tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "lean").mkdir()
            (root / "lean" / "Peluang.lean").write_text(source, encoding="utf-8")
            (root / "THEOREM_MAP.md").write_text(table, encoding="utf-8")
            (root / "Cargo.toml").write_text('[package]\nname = "p"\nversion = "0.1.0"\n', encoding="utf-8")
            tests = root / "tests" / "formalization_lean"
            tests.mkdir(parents=True)
            (tests / "main.rs").write_text("mod a;\n", encoding="utf-8")
            (tests / "a.rs").write_text(witness, encoding="utf-8")
            count, axiom_failures = pa.check(root)
            map_failures = pa.ctm.check(root)
        self.assertEqual((count, axiom_failures, map_failures), (1, [], []))

    def test_current_table_passes_and_each_row_is_checked(self) -> None:
        rows = {i: line for i, (_, line) in pa.ctm.map_rows(REPO / "THEOREM_MAP.md")[0].items()}
        self.assertIn("CategoryTheory.Deterministic.instCopy", rows, f"rows: {sorted(rows)}")
        consts = [f"CONST\t{i}\tPeluang.X\tfalse\t-\t" for i in rows]
        self.assertEqual(pa.unresolved_rows(probe("MODULE\tPeluang.X", *consts), rows), [])
        for lean_id, line in rows.items():
            if lean_id.startswith(pa.MATHLIB_PREFIX):
                continue
            rest = [c for c in consts if c.split("\t")[1] != lean_id]
            failures = pa.unresolved_rows(probe("MODULE\tPeluang.X", *rest), rows)
            self.assertEqual(failures, [f"THEOREM_MAP.md:{line}: `{lean_id}` {NOT_A_CONSTANT}"])

    def test_check_reports_stale_row(self) -> None:
        output = f"{ALLOWED_ROW}\nMODULE\tPeluang\nCONST\tPeluang.instCopy\tPeluang\tfalse\t-\t\n"
        table = (
            "| Lean id | Rust test | anchor |\n|---|---|---|\n"
            "| Peluang.instCopy | tests/formalization_lean/a.rs::f | x |\n"
            "| mathlib:Foo.bar | — | — |\n"
            "| Peluang.instCopyRenamed | tests/formalization_lean/a.rs::g | x |\n"
        )
        with mock.patch.object(pa, "run_lake", lake_ok(output)), tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "lean").mkdir()
            (root / "lean" / "Peluang.lean").write_text("", encoding="utf-8")
            (root / "THEOREM_MAP.md").write_text(table, encoding="utf-8")
            _, failures = pa.check(root)
        self.assertEqual(failures, [f"THEOREM_MAP.md:5: `Peluang.instCopyRenamed` {NOT_A_CONSTANT}"])

    def test_check_reports_missing_map(self) -> None:
        output = f"{ALLOWED_ROW}\nMODULE\tPeluang\n"
        with mock.patch.object(pa, "run_lake", lake_ok(output)), tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "lean").mkdir()
            (root / "lean" / "Peluang.lean").write_text("", encoding="utf-8")
            _, failures = pa.check(root)
        self.assertEqual(failures, [f"{root / 'THEOREM_MAP.md'}: missing"])

    def test_check_reports_malformed_table_line(self) -> None:
        output = f"{ALLOWED_ROW}\nMODULE\tPeluang\n"
        table = "| Lean id | Rust test | anchor |\n|---|---|---|\n| broken row |\n"
        with mock.patch.object(pa, "run_lake", lake_ok(output)), tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "lean").mkdir()
            (root / "lean" / "Peluang.lean").write_text("", encoding="utf-8")
            (root / "THEOREM_MAP.md").write_text(table, encoding="utf-8")
            _, failures = pa.check(root)
        self.assertEqual(failures, ["THEOREM_MAP.md:3: table line is not a row `| <id> | <test> | <anchor> |`"])

    def test_check_reports_missing_table_header(self) -> None:
        output = f"{ALLOWED_ROW}\nMODULE\tPeluang\n"
        table = "# THEOREM_MAP\n\n| Rust test | Lean id | anchor |\n|---|---|---|\n"
        with mock.patch.object(pa, "run_lake", lake_ok(output)), tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "lean").mkdir()
            (root / "lean" / "Peluang.lean").write_text("", encoding="utf-8")
            (root / "THEOREM_MAP.md").write_text(table, encoding="utf-8")
            _, failures = pa.check(root)
        self.assertEqual(failures, ["THEOREM_MAP.md: no `| Lean id` table header"])


class Layout(unittest.TestCase):
    def test_module_names_match_library_files(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            lean = Path(tmp)
            (lean / "Peluang.lean").write_text("", encoding="utf-8")
            (lean / "Peluang" / "Markov").mkdir(parents=True)
            (lean / "Peluang" / "Markov" / "Derived.lean").write_text("", encoding="utf-8")
            (lean / "Peluang" / "AlmostSure.lean").write_text("", encoding="utf-8")
            self.assertEqual(pa.module_names(lean), ["Peluang", "Peluang.AlmostSure", "Peluang.Markov.Derived"])

    def test_module_file(self) -> None:
        self.assertEqual(pa.module_file(Path("/l"), "Peluang"), Path("/l/Peluang.lean"))
        self.assertEqual(pa.module_file(Path("/l"), "Peluang.Markov.Derived"), Path("/l/Peluang/Markov/Derived.lean"))


def lake_stale(calls: list[list[str]]):
    def fake_run_lake(args: list[str], lean_dir: Path, env: dict[str, str] | None = None) -> subprocess.CompletedProcess[str]:
        calls.append(args)
        return subprocess.CompletedProcess(["lake", *args], 1, "", "stale")

    return fake_run_lake


class Freshness(unittest.TestCase):
    def test_stale_check_targets_peluang_and_peluanglint(self) -> None:
        calls: list[list[str]] = []
        with mock.patch.object(pa, "run_lake", lake_stale(calls)), tempfile.TemporaryDirectory() as tmp:
            (Path(tmp) / "lean").mkdir()
            (Path(tmp) / "THEOREM_MAP.md").write_text("| Lean id | Rust test | anchor |\n|---|---|---|\n", encoding="utf-8")
            _, failures = pa.check(Path(tmp))
        self.assertEqual(calls, [["build", "--no-build", "Peluang", "PeluangLint"]], f"lake calls were {calls}")
        self.assertEqual(len(failures), 1, f"failures: {failures}")
        self.assertIn("stale", failures[0])

    def test_stale_build_still_reports_missing_map(self) -> None:
        with mock.patch.object(pa, "run_lake", lake_stale([])), tempfile.TemporaryDirectory() as tmp:
            (Path(tmp) / "lean").mkdir()
            _, failures = pa.check(Path(tmp))
            missing = f"{Path(tmp) / 'THEOREM_MAP.md'}: missing"
        self.assertEqual(len(failures), 2, f"failures: {failures}")
        self.assertIn("stale", failures[0])
        self.assertEqual(failures[1], missing, f"failures: {failures}")

    def test_lake_that_cannot_run_still_reports_missing_map(self) -> None:
        def fake_run_lake(args: list[str], lean_dir: Path, env: dict[str, str] | None = None) -> subprocess.CompletedProcess[str]:
            raise OSError("no lake")

        with mock.patch.object(pa, "run_lake", fake_run_lake), tempfile.TemporaryDirectory() as tmp:
            (Path(tmp) / "lean").mkdir()
            _, failures = pa.check(Path(tmp))
            expected = [f"could not run `lake` in {Path(tmp) / 'lean'}: no lake", f"{Path(tmp) / 'THEOREM_MAP.md'}: missing"]
        self.assertEqual(failures, expected)

    def test_failing_probe_still_reports_missing_map(self) -> None:
        def fake_run_lake(args: list[str], lean_dir: Path, env: dict[str, str] | None = None) -> subprocess.CompletedProcess[str]:
            return subprocess.CompletedProcess(["lake", *args], 1 if args[0] == "env" else 0, "", "boom")

        with mock.patch.object(pa, "run_lake", fake_run_lake), tempfile.TemporaryDirectory() as tmp:
            (Path(tmp) / "lean").mkdir()
            _, failures = pa.check(Path(tmp))
            expected = ["lean exited 1:\nboom", f"{Path(tmp) / 'THEOREM_MAP.md'}: missing"]
        self.assertEqual(failures, expected)


if __name__ == "__main__":
    unittest.main()
