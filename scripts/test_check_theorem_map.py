#!/usr/bin/env python3
"""Fixture tests for check_theorem_map.py: each case is a repo tree in a temp dir."""

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_theorem_map as ctm  # noqa: E402

MAP_HEAD = "# THEOREM_MAP\n\n| Lean id | Rust test | anchor |\n|---|---|---|\n"
LEAN_FILE = "namespace CategoryTheory.Conditional\n\ntheorem unique_as : True := trivial\n\nend CategoryTheory.Conditional\n"
TAG = "/// THEOREM_MAP: CategoryTheory.Conditional.unique_as\n"
TEST_FILE = TAG + "#[test]\nfn unique_as() {}\n"
ROW = "| CategoryTheory.Conditional.unique_as | tests/formalization_lean/conditional_tests.rs::unique_as | — |\n"
MISPLACED = "is not on the line directly above `#[test]` on a fn"


def build(
    root: Path, *, lean: str | None, row: str | None, test: str | None, others: dict[str, str] | None = None
) -> None:
    (root / "THEOREM_MAP.md").write_text(MAP_HEAD + (row or ""), encoding="utf-8")
    if lean is not None:
        d = root / "lean" / "Peluang"
        d.mkdir(parents=True)
        (d / "Conditional.lean").write_text(lean, encoding="utf-8")
    if test is not None:
        d = root / "tests" / "formalization_lean"
        d.mkdir(parents=True)
        (d / "conditional_tests.rs").write_text(test, encoding="utf-8")
    for name, text in (others or {}).items():
        path = root / "tests" / "formalization_lean" / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")


class CheckTheoremMap(unittest.TestCase):
    def run_case(self, **kw: object) -> list[str]:
        with tempfile.TemporaryDirectory() as tmp:
            build(Path(tmp), **kw)
            return ctm.check(Path(tmp))

    def assert_forbidden_text(self, expected: list[str], test: str = TEST_FILE, others: dict[str, str] | None = None) -> None:
        failures = self.run_case(lean=LEAN_FILE, row=ROW, test=test, others=others)
        got = [f.split("/tests/formalization_lean/", 1)[1] for f in failures]
        self.assertEqual(got, [f"{where}: contains the text `f64-prob`" for where in expected], f"failures: {failures}")

    def test_empty_repo_passes(self) -> None:
        self.assertEqual(self.run_case(lean=None, row=None, test=None), [])

    def test_covered_theorem_passes(self) -> None:
        row = "| CategoryTheory.Conditional.unique_as | tests/formalization_lean/conditional_tests.rs::unique_as | Fritz 2020 Prop. 13.7 |\n"
        self.assertEqual(self.run_case(lean=LEAN_FILE, row=row, test=TEST_FILE), [])

    def test_uncovered_theorem_fails(self) -> None:
        failures = self.run_case(lean=LEAN_FILE, row=None, test=None)
        self.assertEqual(len(failures), 1, failures)
        self.assertIn("CategoryTheory.Conditional.unique_as", failures[0])
        self.assertIn("no THEOREM_MAP row", failures[0])

    def test_opt_out_passes(self) -> None:
        lean = LEAN_FILE.replace("theorem unique_as", "-- WITNESS: none (helper lemma)\ntheorem unique_as")
        self.assertEqual(self.run_case(lean=lean, row=None, test=None), [])

    def test_row_without_test_file_fails(self) -> None:
        failures = self.run_case(lean=LEAN_FILE, row=ROW, test=None)
        self.assertEqual(len(failures), 1, failures)
        self.assertIn("does not exist", failures[0])

    def test_row_without_tag_fails(self) -> None:
        failures = self.run_case(lean=LEAN_FILE, row=ROW, test="#[test]\nfn unique_as() {}\n")
        self.assertEqual(len(failures), 1, failures)
        self.assertIn("carries 0", failures[0])

    def test_tag_on_wrong_fn_fails(self) -> None:
        test = TEST_FILE.replace("fn unique_as", "fn other_name")
        failures = self.run_case(lean=LEAN_FILE, row=ROW, test=test)
        self.assertEqual(len(failures), 1, failures)
        self.assertIn("row names `unique_as`", failures[0])

    def test_duplicate_tag_fails(self) -> None:
        failures = self.run_case(lean=LEAN_FILE, row=ROW, test=TEST_FILE + TEST_FILE.replace("fn unique_as", "fn again"))
        self.assertEqual(len(failures), 1, failures)
        self.assertIn("carries 2", failures[0])

    def assert_misplaced(self, test: str, lines: list[int], what: str) -> None:
        failures = self.run_case(lean=LEAN_FILE, row=ROW, test=test)
        got = [f for f in failures if MISPLACED in f]
        self.assertEqual(
            [f.split(": `", 1)[0].rsplit(":", 1)[1] for f in got],
            [str(n) for n in lines],
            f"{what}: misplaced-tag lines; failures: {failures}",
        )

    def test_tag_directly_above_test_attr_passes(self) -> None:
        self.assertEqual(self.run_case(lean=LEAN_FILE, row=ROW, test=TEST_FILE), [])

    def test_tag_above_fn_without_test_attr_is_reported(self) -> None:
        test = TAG + "fn unique_as() {}\n"
        self.assert_misplaced(test, [1], "tag above a fn with no #[test]")
        self.assertIn("carries 0", self.run_case(lean=LEAN_FILE, row=ROW, test=test)[-1])

    def test_tag_separated_from_test_attr_is_reported(self) -> None:
        for between in ("\n", "// note\n", "#[cfg(not(feature = \"parallel\"))]\n", "/// doc\n"):
            with self.subTest(between=between):
                self.assert_misplaced(TAG + between + "#[test]\nfn unique_as() {}\n", [1], f"tag separated by {between!r}")

    def test_lines_allowed_between_test_attr_and_fn_pass(self) -> None:
        for between in (
            "#[cfg(not(feature = \"parallel\"))]\n",
            "#[cfg(not(feature = \"parallel\"))]\n/// doc\n#[allow(dead_code)]\n",
            "\n",
            "// note\n",
            "//// note\n",
        ):
            with self.subTest(between=between):
                test = TAG + "#[test]\n" + between + "fn unique_as() {}\n"
                self.assertEqual(self.run_case(lean=LEAN_FILE, row=ROW, test=test), [])

    def test_fn_forms_pass(self) -> None:
        for header in (
            "pub(crate) fn unique_as() {}",
            "async fn unique_as() {}",
            "fn unique_as<T>() {}",
            "extern fn unique_as() {}",
            "extern \"C\" fn unique_as() {}",
            "pub (crate) fn unique_as() {}",
            "pub(in crate::a)fn unique_as() {}",
        ):
            with self.subTest(header=header):
                test = TAG + "#[test]\n" + header + "\n"
                self.assertEqual(self.run_case(lean=LEAN_FILE, row=ROW, test=test), [], f"fn form {header!r} rejected")

    def test_unsafe_fn_is_reported(self) -> None:
        self.assert_misplaced(TAG + "#[test]\nunsafe fn unique_as() {}\n", [1], "tag above a #[test] unsafe fn")

    def test_path_test_attrs_pass(self) -> None:
        for attr in ("#[tokio::test]", "#[tokio::test(flavor = \"multi_thread\")]"):
            with self.subTest(attr=attr):
                test = TAG + attr + "\nasync fn unique_as() {}\n"
                self.assertEqual(self.run_case(lean=LEAN_FILE, row=ROW, test=test), [], f"{attr} rejected")

    def test_blocking_attrs_are_reported(self) -> None:
        for attr in ("#[ignore]", "#[should_panic]", "#[should_panic(expected = \"x\")]"):
            with self.subTest(attr=attr):
                failures = self.run_case(lean=LEAN_FILE, row=ROW, test=TAG + "#[test]\n" + attr + "\nfn unique_as() {}\n")
                self.assertTrue(any("does not run or does not assert" in f for f in failures), f"{attr} passed: {failures}")

    def test_f64_prob_between_test_attr_and_fn_fails(self) -> None:
        for attr in ("#[cfg(not(feature = \"f64-prob\"))]", "#[cfg(feature = \"f64-prob\")]"):
            with self.subTest(attr=attr):
                self.assert_forbidden_text(["conditional_tests.rs:3"], test=TAG + "#[test]\n" + attr + "\nfn unique_as() {}\n")

    def test_f64_prob_in_inner_attribute_fails(self) -> None:
        main = "#![cfg(not(feature = \"f64-prob\"))]\n\nmod conditional_tests;\n"
        self.assert_forbidden_text(["main.rs:1"], others={"main.rs": main})

    def test_f64_prob_above_the_tag_fails(self) -> None:
        self.assert_forbidden_text(["conditional_tests.rs:1"], test="#[cfg(not(feature = \"f64-prob\"))]\n" + TEST_FILE)

    def test_f64_prob_in_cfg_attr_fails(self) -> None:
        test = TAG + "#[test]\n#[cfg_attr(feature = \"f64-prob\", allow(dead_code))]\nfn unique_as() {}\n"
        self.assert_forbidden_text(["conditional_tests.rs:3"], test=test)

    def test_f64_prob_on_a_mod_fails(self) -> None:
        test = "#[cfg(not(feature = \"f64-prob\"))]\nmod witnesses {\n" + TEST_FILE + "}\n"
        self.assert_forbidden_text(["conditional_tests.rs:1"], test=test)

    def test_f64_prob_in_a_comment_fails(self) -> None:
        self.assert_forbidden_text(["conditional_tests.rs:1"], test="// not in the f64-prob lane\n" + TEST_FILE)

    def test_f64_prob_is_reported_once_per_line_in_every_file(self) -> None:
        others = {"nested/helpers.rs": "\n// f64-prob, f64-prob\n", "main.rs": "// f64-prob\n"}
        self.assert_forbidden_text(["main.rs:1", "nested/helpers.rs:2"], others=others)

    def test_test_attr_with_trailing_comment_passes(self) -> None:
        test = TAG + "#[test] // note\nfn unique_as() {}\n"
        self.assertEqual(self.run_case(lean=LEAN_FILE, row=ROW, test=test), [])

    def test_second_tag_between_test_attr_and_fn_is_reported(self) -> None:
        self.assert_misplaced(TAG + "#[test]\n" + TAG + "fn unique_as() {}\n", [1, 3], "tag inside the attribute block")

    def test_tag_on_last_line_is_reported(self) -> None:
        self.assert_misplaced(TEST_FILE + TAG.rstrip("\n"), [4], "tag at end of file")

    def test_misplaced_duplicate_tag_is_reported(self) -> None:
        test = TEST_FILE + TAG + "fn helper() {}\n"
        failures = self.run_case(lean=LEAN_FILE, row=ROW, test=test)
        self.assertEqual(len(failures), 1, f"failures: {failures}")
        self.assertIn(MISPLACED, failures[0], f"misplaced duplicate tag passed: {failures}")

    def test_mathlib_row_is_optional(self) -> None:
        row = "| mathlib:CategoryTheory.MarkovCategory.eq_discard | — | — |\n"
        self.assertEqual(self.run_case(lean=None, row=row, test=None), [])

    def test_section_end_keeps_namespace(self) -> None:
        lean = "namespace CategoryTheory.Conditional\n\nsection\nvariable (n : Nat)\nend\n\ntheorem unique_as : True := trivial\n\nend CategoryTheory.Conditional\n"
        self.assertEqual(self.run_case(lean=lean, row=ROW, test=TEST_FILE), [])

    def test_named_section_end_pops_section_only(self) -> None:
        lean = "namespace A\nsection S\nend S\nend A\n\nnamespace CategoryTheory.Conditional\ntheorem unique_as : True := trivial\nend CategoryTheory.Conditional\n"
        self.assertEqual(self.run_case(lean=lean, row=ROW, test=TEST_FILE), [])

    def test_multiline_theorem_header_detected(self) -> None:
        lean = "namespace CategoryTheory.Conditional\n\n@[simp]\ntheorem\n  unique_as : True := trivial\n\nend CategoryTheory.Conditional\n"
        failures = self.run_case(lean=lean, row=None, test=None)
        self.assertEqual(len(failures), 1, failures)
        self.assertIn("CategoryTheory.Conditional.unique_as", failures[0])

    def test_opt_out_above_attribute_passes(self) -> None:
        lean = LEAN_FILE.replace("theorem unique_as", "-- WITNESS: none (helper)\n@[simp]\ntheorem unique_as")
        self.assertEqual(self.run_case(lean=lean, row=None, test=None), [])

    def test_duplicate_row_fails(self) -> None:
        row = ROW + "| CategoryTheory.Conditional.unique_as | tests/formalization_lean/other.rs::unique_as | — |\n"
        failures = self.run_case(lean=LEAN_FILE, row=row, test=TEST_FILE)
        self.assertEqual(len(failures), 1, failures)
        self.assertIn("duplicate row", failures[0])

    def decls_in(self, lean: str) -> list[ctm.Decl]:
        with tempfile.TemporaryDirectory() as tmp:
            d = Path(tmp) / "Peluang"
            d.mkdir()
            (d / "X.lean").write_text(lean, encoding="utf-8")
            return ctm.lean_decls([d / "X.lean"])

    def names_in(self, lean: str) -> list[str]:
        return [x.qualified for x in self.decls_in(lean)]

    def test_public_section_end_keeps_namespace(self) -> None:
        for header in ("public section", "@[expose] public section", "public noncomputable section"):
            with self.subTest(header=header):
                lean = f"namespace Peluang\n{header}\ntheorem t1 : True := trivial\nend\ntheorem t2 : True := trivial\nend Peluang\n"
                names = self.names_in(lean)
                self.assertEqual(names, ["Peluang.t1", "Peluang.t2"], f"header {header!r} gave {names}")

    def test_visibility_modifiers_detected(self) -> None:
        lean = "namespace Peluang\npublic theorem a : True := trivial\nprivate theorem b : True := trivial\n@[simp] public theorem c : True := trivial\nend Peluang\n"
        names = self.names_in(lean)
        self.assertEqual(names, ["Peluang.a", "Peluang.b", "Peluang.c"], f"got {names}")

    def test_open_in_and_set_option_in_prefixes_detected(self) -> None:
        lean = "namespace Peluang\nopen Nat in theorem a : True := trivial\nset_option maxHeartbeats 0 in\ntheorem b : True := trivial\nend Peluang\n"
        names = self.names_in(lean)
        self.assertEqual(names, ["Peluang.a", "Peluang.b"], f"got {names}")

    def test_guillemet_name_unquoted(self) -> None:
        names = self.names_in("namespace Peluang\ntheorem «odd name» : True := trivial\nend Peluang\n")
        self.assertEqual(names, ["Peluang.odd name"], f"got {names}")

    def test_opt_out_across_docstring_and_multiline_attribute(self) -> None:
        lean = "namespace Peluang\n-- WITNESS: none (helper)\n/-- Doc. -/\n@[simp,\n  reducible]\ntheorem h : True := trivial\n\ntheorem k : True := trivial\nend Peluang\n"
        got = [(x.qualified, x.opted_out) for x in self.decls_in(lean)]
        self.assertEqual(got, [("Peluang.h", True), ("Peluang.k", False)], f"got {got}")

    def test_opt_out_does_not_leak_past_code_ending_in_bracket(self) -> None:
        lean = "namespace Peluang\n-- WITNESS: none (r)\ntheorem a : True ∧ True := by simp [and_self]\n\ntheorem b : True := trivial\nend Peluang\n"
        got = [(x.qualified, x.opted_out) for x in self.decls_in(lean)]
        self.assertEqual(got, [("Peluang.a", True), ("Peluang.b", False)], f"got {got}")

    def test_opt_out_does_not_leak_past_inline_attribute_declaration(self) -> None:
        lean = "namespace Peluang\n-- WITNESS: none (r)\n@[simp] theorem a : True := by simp [h]\ntheorem b : True := trivial\nend Peluang\n"
        got = [(x.qualified, x.opted_out) for x in self.decls_in(lean)]
        self.assertEqual(got, [("Peluang.a", True), ("Peluang.b", False)], f"got {got}")

    def test_opt_out_does_not_leak_past_multiline_proof_ending_in_comma(self) -> None:
        lean = "namespace Peluang\n-- WITNESS: none (r)\ntheorem a : True := by simp [foo,\n    bar]\ntheorem b : True := trivial\nend Peluang\n"
        got = [(x.qualified, x.opted_out) for x in self.decls_in(lean)]
        self.assertEqual(got, [("Peluang.a", True), ("Peluang.b", False)], f"got {got}")

    def test_library_decls_include_root_file(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            lean = Path(tmp)
            (lean / "Peluang.lean").write_text("theorem Peluang.rootThm : True := trivial\n", encoding="utf-8")
            (lean / "Peluang").mkdir()
            (lean / "Peluang" / "A.lean").write_text("theorem Peluang.a : True := trivial\n", encoding="utf-8")
            names = [x.qualified for x in ctm.library_decls(lean)]
        self.assertEqual(names, ["Peluang.rootThm", "Peluang.a"], f"got {names}")

    def test_root_file_theorem_needs_row(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "THEOREM_MAP.md").write_text(MAP_HEAD, encoding="utf-8")
            (root / "lean").mkdir()
            (root / "lean" / "Peluang.lean").write_text("theorem Peluang.rootThm : True := trivial\n", encoding="utf-8")
            failures = ctm.check(root)
        self.assertEqual(len(failures), 1, failures)
        self.assertIn("Peluang.rootThm", failures[0])

    def test_comment_text_is_not_scanned(self) -> None:
        lean = "/-!\ntheorem fake : False\nnamespace Bogus\n-/\nnamespace Peluang\n-- theorem alsoFake : False\ntheorem real : True := trivial\nend Peluang\n"
        names = self.names_in(lean)
        self.assertEqual(names, ["Peluang.real"], f"got {names}")

    def test_mutual_end_keeps_namespace(self) -> None:
        lean = "namespace Peluang\nmutual\ntheorem a : True := trivial\ntheorem b : True := trivial\nend\ntheorem c : True := trivial\nend Peluang\n"
        names = self.names_in(lean)
        self.assertEqual(names, ["Peluang.a", "Peluang.b", "Peluang.c"], f"got {names}")

    def test_root_prefix_drops_namespace(self) -> None:
        names = self.names_in("namespace Peluang\ntheorem _root_.Foo.bar : True := trivial\nend Peluang\n")
        self.assertEqual(names, ["Foo.bar"], f"got {names}")

    def test_nonrec_and_partial_modifiers_detected(self) -> None:
        lean = "namespace Peluang\nnonrec theorem a : True := trivial\n@[simp] private nonrec theorem b : True := trivial\nend Peluang\n"
        names = self.names_in(lean)
        self.assertEqual(names, ["Peluang.a", "Peluang.b"], f"got {names}")

    def test_opt_out_still_read_from_raw_comment(self) -> None:
        lean = "namespace Peluang\n-- WITNESS: none (helper)\ntheorem h : True := trivial\nend Peluang\n"
        self.assertEqual([(x.qualified, x.opted_out) for x in self.decls_in(lean)], [("Peluang.h", True)])

    def test_bad_test_column_fails(self) -> None:
        row = "| CategoryTheory.Conditional.unique_as | conditional_tests.rs::unique_as | — |\n"
        failures = self.run_case(lean=LEAN_FILE, row=row, test=TEST_FILE)
        self.assertEqual(len(failures), 1, failures)
        self.assertIn("is not `tests/formalization_lean/", failures[0])


if __name__ == "__main__":
    unittest.main()
