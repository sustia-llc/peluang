#!/usr/bin/env python3
"""Unit tests for check_peluangtest (no Lean needed)."""

from __future__ import annotations

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_peluangtest as cp  # noqa: E402

LAKEFILE = """package «Peluang» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`weak.linter.style.header, false⟩]
"""
BASELINE = "_private.Lean.DocString.Extension.0.Lean.moduleDocExt"


def lines(*rows: str) -> str:
    return "".join(f"{r}\n" for r in rows)


def example_report(*rows: str) -> cp.ExampleReport:
    return cp.parse_example_output(lines(*rows))


class ParseImportOutput(unittest.TestCase):
    def test_rows(self) -> None:
        r = cp.parse_import_output(
            lines(
                "MODULE\tPeluangTest.A",
                "CONST\tPeluangTest.A\t_private.PeluangTest.A.0.foo",
                "EXTRA\tPeluangTest.A\tbar",
                f"ENTRIES\tPeluangTest.A\t{BASELINE}\t1",
                "DONE",
            )
        )
        self.assertEqual(r.modules, {"PeluangTest.A"})
        self.assertEqual(r.consts, [("PeluangTest.A", "_private.PeluangTest.A.0.foo")])
        self.assertEqual(r.extras, [("PeluangTest.A", "bar")])
        self.assertEqual(r.entries, [("PeluangTest.A", BASELINE, 1)])
        self.assertTrue(r.done)

    def test_malformed_rows_ignored(self) -> None:
        r = cp.parse_import_output("warning: x\nCONST\tonly\nENTRIES\tm\text\tmany\n")
        self.assertEqual((r.modules, r.consts, r.entries, r.done), (set(), [], [], False))


class ParseExampleOutput(unittest.TestCase):
    def test_rows(self) -> None:
        r = example_report(
            "FINAL\tM\tfoo\t",
            "HIDDEN\tM\t27\tCategoryTheory._example\tpropext,Classical.choice,Quot.sound",
            "EXAMPLES\tM\t1",
            "MSG\tM\terror\t5\tUnknown identifier `α`\\n\\nNote: a\\\\b",
            "DONE\tM",
        )
        self.assertEqual(r.finals, [("foo", ())])
        self.assertEqual(r.hidden, [cp.Hidden(27, "CategoryTheory._example", ("propext", "Classical.choice", "Quot.sound"))])
        self.assertEqual(r.examples, 1)
        self.assertEqual(r.messages, [("error", 5, "Unknown identifier `α`\n\nNote: a\\b")])
        self.assertTrue(r.done)

    def test_escaped_tab_and_line_separators_keep_the_row(self) -> None:
        r = cp.parse_example_output("MSG\tM\terror\t5\ta\\tb\\rc\x1cd e\nDONE\tM\n")
        self.assertEqual(r.messages, [("error", 5, "a\tb\rc\x1cd e")])

    def test_missing_examples_row_is_none(self) -> None:
        self.assertIsNone(example_report("DONE\tM").examples)


class HiddenExamples(unittest.TestCase):
    def test_counts_example_constants_not_their_aux_axioms(self) -> None:
        r = example_report(
            "HIDDEN\tM\t1\tCategoryTheory._example\t",
            "HIDDEN\tM\t2\t_private.M.0._example\t_private.M.0._example._native.native_decide.ax_1",
            "HIDDEN\tM\t2\t_private.M.0._example._native.native_decide.ax_1\t_private.M.0._example._native.native_decide.ax_1",
            "HIDDEN\tM\t3\t_private.M.0._eval\t",
        )
        self.assertEqual(cp.hidden_examples(r), 2)


class Layout(unittest.TestCase):
    def test_test_files_root_then_tree(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            lean = Path(tmp)
            (lean / "PeluangTest" / "Markov").mkdir(parents=True)
            (lean / "Peluang").mkdir()
            for rel in ["PeluangTest.lean", "PeluangTest/Lint.lean", "PeluangTest/Markov/Derived.lean", "Peluang/X.lean", "Peluang.lean"]:
                (lean / rel).write_text("", encoding="utf-8")
            (lean / "PeluangTest" / "notes.md").write_text("", encoding="utf-8")
            files = cp.library_files(lean, cp.TEST_ROOT)
            self.assertEqual(
                [p.relative_to(lean).as_posix() for p in files],
                ["PeluangTest.lean", "PeluangTest/Lint.lean", "PeluangTest/Markov/Derived.lean"],
            )
            self.assertEqual(cp.module_names(lean, cp.TEST_ROOT), ["PeluangTest", "PeluangTest.Lint", "PeluangTest.Markov.Derived"])

    def test_no_test_files(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            self.assertEqual(cp.library_files(Path(tmp), cp.TEST_ROOT), [])

    def test_lean_options_from_lakefile(self) -> None:
        self.assertEqual(
            cp.lean_options(LAKEFILE),
            ["autoImplicit=false", "weak.linter.mathlibStandardSet=true", "weak.linter.style.header=false"],
        )

    def test_lean_options_absent_or_repeated_is_none(self) -> None:
        self.assertIsNone(cp.lean_options("package «P» where\n"))
        repeated = LAKEFILE + "lean_lib «PeluangTest» where\n  leanOptions := #[⟨`autoImplicit, true⟩]\n"
        self.assertIsNone(cp.lean_options(repeated))

    def test_lean_options_ignores_commented_block(self) -> None:
        commented = "-- leanOptions := #[⟨`autoImplicit, true⟩]\n/- leanOptions := #[] -/\n" + LAKEFILE
        self.assertEqual(
            cp.lean_options(commented),
            ["autoImplicit=false", "weak.linter.mathlibStandardSet=true", "weak.linter.style.header=false"],
        )

    def test_lean_options_string_value_with_bracket(self) -> None:
        text = 'package «P» where\n  leanOptions := #[⟨`pp.foo, "a]=b"⟩, ⟨`autoImplicit, false⟩]\n'
        self.assertEqual(cp.lean_options(text), ["pp.foo=a]=b", "autoImplicit=false"])

    def test_commented_entry_inside_block_is_ignored(self) -> None:
        text = "package «P» where\n  leanOptions := #[ -- ⟨`autoImplicit, true⟩,\n    ⟨`autoImplicit, false⟩]\n"
        self.assertEqual(cp.lean_options(text), ["autoImplicit=false"])
        text = "package «P» where\n  leanOptions := #[ /- ⟨`autoImplicit, true⟩, -/ ⟨`foo, someIdent⟩]\n"
        self.assertIsNone(cp.lean_options(text), "a commented literal entry replaced an unparsed real entry")

    def test_comment_straddling_entries_keeps_real_entry(self) -> None:
        text = 'package «P» where\n  leanOptions := #[ /- ⟨`a, "-/ ⟨`b, "⟩"⟩]\n'
        self.assertEqual(cp.lean_options(text), ["b=⟩"], "a match starting in the comment consumed the real entry")

    def test_other_option_fields_are_none(self) -> None:
        for field in ("moreLeanArgs", "weakLeanArgs", "moreServerOptions", "moreServerArgs"):
            with self.subTest(field=field):
                text = LAKEFILE + f'\nlean_lib «PeluangTest» where\n  {field} := #["-DautoImplicit=true"]\n'
                self.assertIsNone(cp.lean_options(text), f"{field} was accepted")
        self.assertIsNotNone(cp.lean_options(LAKEFILE + "-- moreLeanArgs := #[]\n"))

    def test_lean_options_unparsed_entry_is_none(self) -> None:
        text = "package «P» where\n  leanOptions := #[⟨`maxHeartbeats, .ofNat 400000⟩, ⟨`autoImplicit, false⟩]\n"
        self.assertIsNone(cp.lean_options(text))


class EvaluateImports(unittest.TestCase):
    def test_clean_passes(self) -> None:
        moved = "_private.Lean.Moved.Path.0.Lean.modPkgExt"
        r = cp.parse_import_output(
            lines("MODULE\tPeluangTest", f"ENTRIES\tPeluangTest\t{BASELINE}\t1", f"ENTRIES\tPeluangTest\t{moved}\t1", "DONE")
        )
        self.assertEqual(cp.evaluate_imports(r, ["PeluangTest"]), [])

    def test_constant_extra_and_extension_fail(self) -> None:
        r = cp.parse_import_output(
            lines(
                "MODULE\tPeluangTest.A",
                "CONST\tPeluangTest.A\t_private.PeluangTest.A.0.foo",
                "EXTRA\tPeluangTest.A\tbar",
                "ENTRIES\tPeluangTest.A\tLean.Meta.simpExtension\t1",
                "ENTRIES\tPeluangTest.A\tLean.indirectModUseExt\t2",
                "DONE",
            )
        )
        self.assertEqual(
            cp.evaluate_imports(r, ["PeluangTest.A"]),
            [
                "`PeluangTest.A`: defines constant `foo` (_private.PeluangTest.A.0.foo)",
                "`PeluangTest.A`: defines extra constant `bar` (bar)",
                "`PeluangTest.A`: adds 1 entry to extension `Lean.Meta.simpExtension`",
                "`PeluangTest.A`: adds 2 entries to extension `Lean.indirectModUseExt`",
            ],
        )

    def test_foreign_extension_with_allowed_last_component_fails(self) -> None:
        r = cp.parse_import_output(lines("MODULE\tPeluangTest", "ENTRIES\tPeluangTest\tMathlib.Foo.extraModUses\t1", "DONE"))
        failures = cp.evaluate_imports(r, ["PeluangTest"])
        self.assertEqual(len(failures), 1, f"failures: {failures}")
        self.assertIn("Mathlib.Foo.extraModUses", failures[0])

    def test_unloaded_module_and_truncated_output_fail(self) -> None:
        r = cp.parse_import_output(lines("MODULE\tPeluangTest"))
        self.assertEqual(
            cp.evaluate_imports(r, ["PeluangTest", "PeluangTest.B"]),
            ["import check: output ended before DONE", "`PeluangTest.B`: not loaded by the import check"],
        )


class EvaluateOptions(unittest.TestCase):
    OPTS = ["autoImplicit=false", "weak.linter.mathlibStandardSet=true"]

    def test_all_set_passes(self) -> None:
        r = example_report("OPTION\tM\tweak.linter.mathlibStandardSet\tset", "OPTION\tM\tautoImplicit\tset", "DONE\tM")
        self.assertEqual(cp.evaluate_options(r, "f.lean", self.OPTS), [])

    def test_dropped_option_fails(self) -> None:
        r = example_report("OPTION\tM\tautoImplicit\tset", "OPTION\tM\tweak.linter.mathlibStandardSet\tdropped", "DONE\tM")
        failures = cp.evaluate_options(r, "f.lean", self.OPTS)
        self.assertEqual(len(failures), 1, f"failures: {failures}")
        self.assertIn("`weak.linter.mathlibStandardSet` was dropped", failures[0])

    def test_repeated_option_passes(self) -> None:
        r = example_report("OPTION\tM\tautoImplicit\tset", "DONE\tM")
        self.assertEqual(cp.evaluate_options(r, "f.lean", ["autoImplicit=false", "autoImplicit=false"]), [])

    def test_weak_option_dropped_control(self) -> None:
        dropped = example_report("OPTION\tM\tautoImplicit\tset", "OPTION\tM\tweak.linter.mathlibStandardSet\tdropped")
        all_set = example_report("OPTION\tM\tautoImplicit\tset", "OPTION\tM\tweak.linter.mathlibStandardSet\tset")
        self.assertTrue(cp.weak_option_dropped(dropped, self.OPTS))
        self.assertFalse(cp.weak_option_dropped(all_set, self.OPTS), "an all-set report passed the control")
        self.assertTrue(cp.weak_option_dropped(all_set, ["autoImplicit=false"]))

    def test_missing_option_row_fails(self) -> None:
        r = example_report("OPTION\tM\tautoImplicit\tset", "DONE\tM")
        failures = cp.evaluate_options(r, "f.lean", self.OPTS)
        self.assertEqual(len(failures), 1, f"failures: {failures}")
        self.assertIn("reported options", failures[0])


class EvaluateExamples(unittest.TestCase):
    def test_clean_passes(self) -> None:
        r = example_report("HIDDEN\tM\t3\tX._example\tpropext,Quot.sound", "EXAMPLES\tM\t1", "MSG\tM\tinformation\t4\tok", "DONE\tM")
        self.assertEqual(cp.evaluate_examples(r, "f.lean"), [])

    def test_native_axiom_fails_and_is_plant_report(self) -> None:
        ax = "_private.M.0._example._native.native_decide.ax_1"
        r = example_report(f"HIDDEN\tM\t5\t_private.M.0._example\t{ax}", "EXAMPLES\tM\t1", "DONE\tM")
        failures = cp.evaluate_examples(r, "plant")
        self.assertEqual(failures, [f"plant:5: `_example` depends on {ax} (allowed: Classical.choice, Quot.sound, propext)"])
        self.assertTrue(cp.plant_reported(r))

    def test_plant_not_reported_on_clean_output(self) -> None:
        r = example_report("HIDDEN\tM\t5\t_private.M.0._example\t", "EXAMPLES\tM\t1", "DONE\tM")
        self.assertFalse(cp.plant_reported(r))

    def test_plant_read_from_axioms_not_messages(self) -> None:
        r = example_report("EXAMPLES\tM\t1", "MSG\tM\terror\t5\tx._native.native_decide.ax_1", "DONE\tM")
        self.assertFalse(cp.plant_reported(r), "a message holding the axiom name counted as a plant report")

    def test_sorry_fails(self) -> None:
        r = example_report("HIDDEN\tM\t2\tX._example\tsorryAx", "EXAMPLES\tM\t1", "DONE\tM")
        self.assertEqual(cp.evaluate_examples(r, "f.lean"), ["f.lean:2: `X._example` depends on sorryAx (allowed: Classical.choice, Quot.sound, propext)"])

    def test_final_constant_fails(self) -> None:
        r = example_report("FINAL\tM\t_private.M.0.foo\t", "EXAMPLES\tM\t0", "DONE\tM")
        self.assertEqual(cp.evaluate_examples(r, "f.lean"), ["f.lean: constant `foo` survives in the file's environment (no axioms)"])

    def test_error_message_fails_and_warning_does_not(self) -> None:
        r = example_report("EXAMPLES\tM\t0", "MSG\tM\terror\t7\tbad\\nthing", "MSG\tM\twarning\t8\tmeh", "DONE\tM")
        self.assertEqual(cp.evaluate_examples(r, "f.lean"), ["f.lean:7: error: bad\nthing"])

    def test_count_mismatch_fails(self) -> None:
        r = example_report("HIDDEN\tM\t3\tX._example\t", "EXAMPLES\tM\t2", "DONE\tM")
        self.assertEqual(cp.evaluate_examples(r, "f.lean"), ["f.lean: 1 hidden `_example` constant(s) for 2 `example` command(s)"])

    def test_missing_examples_and_done_fail(self) -> None:
        self.assertEqual(
            cp.evaluate_examples(example_report(), "f.lean"),
            ["f.lean: example check output ended before DONE", "f.lean: example check printed no EXAMPLES row"],
        )


class DeclPlant(unittest.TestCase):
    def test_needs_both_import_and_final_rows(self) -> None:
        c = cp.DECL_PLANT_CONST
        imports = cp.parse_import_output(lines(f"MODULE\t{cp.DECL_PLANT_MODULE}", f"CONST\t{cp.DECL_PLANT_MODULE}\t{c}", "DONE"))
        report = example_report(f"FINAL\tM\t{c}\t", "EXAMPLES\tM\t0", "DONE\tM")
        self.assertTrue(cp.decl_plant_reported(imports, report))
        self.assertFalse(cp.decl_plant_reported(cp.ImportReport(), report))
        self.assertFalse(cp.decl_plant_reported(imports, cp.ExampleReport()))


class Reporting(unittest.TestCase):
    def test_count_line(self) -> None:
        s = cp.Summary(examples={"lean/PeluangTest.lean": 0, "lean/PeluangTest/A.lean": 3}, constants=0, plant=True, decl_plant=True)
        self.assertEqual(
            cp.count_line(s),
            "check_peluangtest: 2 file(s), 3 example(s), 0 constant(s), plant reported, declaration plant reported "
            "(lean/PeluangTest.lean 0, lean/PeluangTest/A.lean 3)",
        )
        s.plant = False
        self.assertIn(", plant not reported", cp.count_line(s))
        s.decl_plant = False
        self.assertIn("declaration plant not reported", cp.count_line(s))

    def test_exit_failure(self) -> None:
        ok = subprocess.CompletedProcess(["lake"], 0, "", "")
        bad = subprocess.CompletedProcess(["lake"], 1, "out\n", "err\n")
        self.assertEqual(cp.exit_failure(ok, "x"), [])
        self.assertEqual(cp.exit_failure(bad, "x"), ["x: lean exited 1:\nout\nerr"])


class Freshness(unittest.TestCase):
    def test_stale_build_refuses_before_any_lean_run(self) -> None:
        calls: list[list[str]] = []

        def fake_run_lake(
            args: list[str], lean_dir: Path, env: dict[str, str] | None = None
        ) -> subprocess.CompletedProcess[str]:
            calls.append(args)
            return subprocess.CompletedProcess(["lake", *args], 1, "", "stale")

        with mock.patch.object(cp, "run_lake", fake_run_lake), tempfile.TemporaryDirectory() as tmp:
            lean = Path(tmp) / "lean"
            lean.mkdir()
            (lean / "lakefile.lean").write_text(LAKEFILE, encoding="utf-8")
            (lean / "PeluangTest.lean").write_text("", encoding="utf-8")
            s = cp.check(Path(tmp))
        self.assertEqual(calls, [["build", "--no-build", "PeluangTest"]], f"lake calls were {calls}")
        self.assertEqual(len(s.failures), 1, f"failures: {s.failures}")
        self.assertIn("stale", s.failures[0])

    def test_missing_lakefile_is_a_failure_line(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            lean = Path(tmp) / "lean"
            lean.mkdir()
            (lean / "PeluangTest.lean").write_text("", encoding="utf-8")
            s = cp.check(Path(tmp))
        self.assertEqual(len(s.failures), 1, f"failures: {s.failures}")
        self.assertIn("lakefile.lean", s.failures[0])

    def test_lakefile_without_options_refuses_before_any_lean_run(self) -> None:
        calls: list[list[str]] = []

        def fake_run_lake(args: list[str], lean_dir: Path, env: dict[str, str] | None = None) -> None:
            calls.append(args)

        with mock.patch.object(cp, "run_lake", fake_run_lake), tempfile.TemporaryDirectory() as tmp:
            lean = Path(tmp) / "lean"
            lean.mkdir()
            (lean / "lakefile.lean").write_text("package «P» where\n", encoding="utf-8")
            (lean / "PeluangTest.lean").write_text("", encoding="utf-8")
            s = cp.check(Path(tmp))
        self.assertEqual(calls, [], f"lake calls were {calls}")
        self.assertEqual(len(s.failures), 1, f"failures: {s.failures}")
        self.assertIn("leanOptions", s.failures[0])


if __name__ == "__main__":
    unittest.main()
