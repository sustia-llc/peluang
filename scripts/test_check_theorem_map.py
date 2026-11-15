#!/usr/bin/env python3
"""Fixture tests for check_theorem_map.py: each case is a repo tree in a temp dir."""

from __future__ import annotations

import contextlib
import io
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_theorem_map as ctm  # noqa: E402

MAP_HEAD = "# THEOREM_MAP\n\n| Lean id | Rust test | anchor |\n|---|---|---|\n"
LEAN_FILE = "namespace CategoryTheory.Conditional\n\ntheorem unique_as : True := trivial\n\nend CategoryTheory.Conditional\n"
TAG = "/// THEOREM_MAP: CategoryTheory.Conditional.unique_as\n"
TEST_FILE = TAG + "#[test]\nfn unique_as() {}\n"
ROW = "| CategoryTheory.Conditional.unique_as | tests/formalization_lean/conditional_tests.rs::unique_as | — |\n"
MISPLACED = "is not on the line directly above `#[test]` on a fn"
CARGO = '[package]\nname = "x"\n'
UNREACHED = "holds a THEOREM_MAP tag and no mod declaration from a test target root reaches it"


def build(
    root: Path,
    *,
    lean: str | None,
    row: str | None,
    test: str | None,
    others: dict[str, str] | None = None,
    cargo: str | None = CARGO,
    head: str = MAP_HEAD,
) -> None:
    """The repo tree of one case. `cargo=None` writes no Cargo.toml. With `test`, it writes `conditional_tests.rs`
    and, unless `others` has one, a `main.rs` declaring `mod conditional_tests;`."""
    (root / "THEOREM_MAP.md").write_text(head + (row or ""), encoding="utf-8")
    if cargo is not None:
        (root / "Cargo.toml").write_text(cargo, encoding="utf-8")
    if lean is not None:
        d = root / "lean" / "Peluang"
        d.mkdir(parents=True)
        (d / "Conditional.lean").write_text(lean, encoding="utf-8")
    if test is not None:
        d = root / "tests" / "formalization_lean"
        d.mkdir(parents=True)
        (d / "conditional_tests.rs").write_text(test, encoding="utf-8")
        if "main.rs" not in (others or {}):
            (d / "main.rs").write_text("mod conditional_tests;\n", encoding="utf-8")
    for name, text in (others or {}).items():
        path = root / "tests" / "formalization_lean" / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")


class CheckTheoremMap(unittest.TestCase):
    def run_case(self, **kw: object) -> list[str]:
        with tempfile.TemporaryDirectory() as tmp:
            build(Path(tmp), **kw)
            return ctm.check(Path(tmp))

    def assert_forbidden_text(
        self,
        expected: list[str],
        test: str = TEST_FILE,
        others: dict[str, str] | None = None,
        matched: str = "`cfg`, `f64-prob`",
    ) -> None:
        failures = self.run_case(lean=LEAN_FILE, row=ROW, test=test, others=others)
        got = [f.partition("/tests/formalization_lean/")[2] or f for f in failures]
        self.assertEqual(got, [f"{where}: contains the text {matched}" for where in expected], f"failures: {failures}")

    def test_empty_repo_passes(self) -> None:
        self.assertEqual(self.run_case(lean=None, row=None, test=None, cargo=CARGO), [])

    def test_missing_cargo_toml_fails(self) -> None:
        failures = self.run_case(lean=None, row=None, test=None, cargo=None)
        self.assertEqual([f.rsplit("/", 1)[-1] for f in failures], ["Cargo.toml: missing"], f"failures: {failures}")

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
            "#[allow(dead_code)]\n",
            "#[allow(dead_code)]\n/// doc\n#[allow(dead_code)]\n",
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
        self.assert_forbidden_text(
            ["conditional_tests.rs:1"], test="// not in the f64-prob lane\n" + TEST_FILE, matched="`f64-prob`"
        )

    def test_f64_prob_is_reported_once_per_line_in_every_file(self) -> None:
        others = {"nested/helpers.rs": "\n// f64-prob, f64-prob\n", "main.rs": "// f64-prob\nmod conditional_tests;\n"}
        self.assert_forbidden_text(["main.rs:1", "nested/helpers.rs:2"], others=others, matched="`f64-prob`")

    def test_cfg_with_another_feature_fails(self) -> None:
        test = TAG + "#[test]\n#[cfg(not(feature = \"parallel\"))]\nfn unique_as() {}\n"
        self.assert_forbidden_text(["conditional_tests.rs:3"], test=test, matched="`cfg`")

    def test_cfg_attr_with_another_feature_fails(self) -> None:
        test = TAG + "#[test]\n#[cfg_attr(feature = \"parallel\", ignore)]\nfn unique_as() {}\n"
        self.assert_forbidden_text(["conditional_tests.rs:3"], test=test, matched="`cfg`")

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
            (root / "Cargo.toml").write_text(CARGO, encoding="utf-8")
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

    def gated_failures(self, cargo: str) -> list[str]:
        main = {"main.rs": "mod conditional_tests;\n"}
        failures = self.run_case(lean=LEAN_FILE, row=ROW, test=TEST_FILE, others=main, cargo=cargo)
        return [f for f in failures if "Cargo.toml" in f]

    def test_required_features_on_the_witness_target_fail(self) -> None:
        for table in (
            '[[test]]\nname = "formalization_lean"\npath = "tests/formalization_lean/main.rs"\nrequired-features = ["parallel"]\n',
            '[[test]]\nname = "formalization_lean"\nrequired-features = ["parallel"]\n',
            '[[test]]\nname = "conditional"\npath = "tests/formalization_lean/conditional_tests.rs"\nrequired-features = ["async"]\n',
        ):
            with self.subTest(table=table):
                failures = self.gated_failures("[package]\nname = \"x\"\n\n" + table)
                self.assertEqual(len(failures), 1, f"failures: {failures}")
                name = table.split('name = "', 1)[1].split('"', 1)[0]
                self.assertIn(f"[[test]] `{name}` holds THEOREM_MAP witnesses", failures[0], failures)

    def test_ungated_or_unrelated_targets_pass(self) -> None:
        for table in (
            '[[test]]\nname = "formalization_lean"\npath = "tests/formalization_lean/main.rs"\n',
            '[[test]]\nname = "formalization_lean"\npath = "tests/formalization_lean/main.rs"\nrequired-features = []\n',
            '[[test]]\nname = "exec"\npath = "tests/exec.rs"\nrequired-features = ["async"]\n',
            '[[test]]\nname = "other"\npath = "tests/formalization_lean/other.rs"\nrequired-features = ["async"]\n',
            "",
        ):
            with self.subTest(table=table):
                self.assertEqual(self.gated_failures("[package]\nname = \"x\"\n\n" + table), [])

    def test_invalid_cargo_toml_fails(self) -> None:
        failures = self.gated_failures("[package\n")
        self.assertEqual(len(failures), 1, f"failures: {failures}")
        self.assertIn("not valid TOML", failures[0])

    def unreached(self, failures: list[str]) -> list[str]:
        return [f.partition("/tests/formalization_lean/")[2] for f in failures if UNREACHED in f]

    def test_test_root_resolves_mod_against_its_own_directory(self) -> None:
        cargo = CARGO + 'autotests = false\n\n[[test]]\nname = "fl"\npath = "tests/formalization_lean/root.rs"\n'
        others = {"root.rs": "mod conditional_tests;\n"}
        failures = self.run_case(lean=LEAN_FILE, row=ROW, test=TEST_FILE, others=others, cargo=cargo)
        self.assertEqual(failures, [], "a [[test]] root named root.rs resolves `mod conditional_tests;` to its sibling")

    def test_non_root_file_resolves_mod_against_its_stem_directory(self) -> None:
        tagged = TAG + "#[test]\nfn inner() {}\n"
        for where, expected in (("nested/inner.rs", []), ("inner.rs", [f"inner.rs: {UNREACHED}"])):
            with self.subTest(where=where):
                others = {"main.rs": "mod nested;\n", "nested.rs": "mod inner;\n", where: tagged}
                failures = self.run_case(lean=None, row=None, test=None, others=others)
                self.assertEqual(self.unreached(failures), expected, f"inner at {where}: failures {failures}")

    def test_path_attribute_is_followed(self) -> None:
        others = {
            "main.rs": '#[path = "deep/witness.rs"]\n// note\nmod witness;\n',
            "deep/witness.rs": "mod more;\n" + TAG + "#[test]\nfn witness() {}\n",
            "deep/more.rs": TAG + "#[test]\nfn more() {}\n",
        }
        failures = self.run_case(lean=None, row=None, test=None, others=others)
        self.assertEqual(failures, [], "a #[path] module and its own `mod more;` child are reached")

    def test_path_attribute_does_not_carry_past_an_item(self) -> None:
        others = {
            "main.rs": '#[path = "deep/witness.rs"]\nuse std::fmt;\nmod witness;\n',
            "deep/witness.rs": TAG + "#[test]\nfn witness() {}\n",
        }
        failures = self.run_case(lean=None, row=None, test=None, others=others)
        self.assertEqual(self.unreached(failures), [f"deep/witness.rs: {UNREACHED}"], f"failures: {failures}")

    def tree_unreached(self, files: dict[str, str]) -> list[str]:
        """The unreached tagged files of a tree holding only `files` (paths under `tests/`) and CARGO."""
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            build(root, lean=None, row=None, test=None)
            for name, text in files.items():
                path = root / "tests" / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text, encoding="utf-8")
            failures = ctm.check(root)
        others = [f for f in failures if UNREACHED not in f]
        self.assertEqual(others, [], f"unexpected failures: {failures}")
        return [f.partition("/tests/")[2].removesuffix(f": {UNREACHED}") for f in failures]

    def test_commented_out_mod_is_unreached(self) -> None:
        tagged = TAG + "#[test]\nfn w() {}\n"
        for main, expected in (
            ("/*\nmod w;\n*/\n", ["formalization_lean/w.rs"]),
            ("/* outer /* nested */\nmod w;\n*/\n", ["formalization_lean/w.rs"]),
            ("/* end;\nmod w;\n*/\n", ["formalization_lean/w.rs"]),
            ("/* outer /* nested */ end;\nmod w;\n*/\n", ["formalization_lean/w.rs"]),
            ("// mod w;\n", ["formalization_lean/w.rs"]),
            ("// a brace {\nmod w;\n", []),
            ("/* note */ mod w;\n", []),
            ("mod /* note */ w;\n", []),
        ):
            with self.subTest(main=main):
                got = self.tree_unreached({"formalization_lean/main.rs": main, "formalization_lean/w.rs": tagged})
                self.assertEqual(got, expected, f"main.rs {main!r}")

    def test_cfg_gated_mod_is_unreached(self) -> None:
        tagged = TAG + "#[test]\nfn w() {}\n"
        path = '#[path = "formalization_lean/w.rs"]'
        for root_file, expected in (
            (f'#[cfg(feature = "x")] {path} mod w;\n', ["formalization_lean/w.rs"]),
            (f'#[cfg(feature = "x")]\n{path}\nmod w;\n', ["formalization_lean/w.rs"]),
            (f'{path}\n#[cfg(feature = "x")]\nmod w;\n', ["formalization_lean/w.rs"]),
            ("#[cfg(test)]\nmod formalization_lean {\n    mod w;\n}\n", ["formalization_lean/w.rs"]),
            ("#[cfg(test)]\nmod formalization_lean {\n    mod inner {\n        #[path = \"../w.rs\"] mod w;\n    }\n}\n",
             ["formalization_lean/w.rs"]),
            (f"{path} mod w;\n", []),
            ("mod formalization_lean {\n    mod w;\n}\n", []),
            ('#[cfg_attr(feature = "x", allow(dead_code))]\n' + f"{path} mod w;\n", []),
        ):
            with self.subTest(root_file=root_file):
                got = self.tree_unreached({"witness.rs": root_file, "formalization_lean/w.rs": tagged})
                self.assertEqual(got, expected, f"tests/witness.rs {root_file!r}")

    def test_same_line_path_attribute_is_followed(self) -> None:
        tagged = TAG + "#[test]\nfn w() {}\n"
        for main in ('#[path = "deep/w.rs"] mod w;\n', '#[allow(unused)] #[path = "deep/w.rs"] pub mod w;\n'):
            with self.subTest(main=main):
                got = self.tree_unreached({"formalization_lean/main.rs": main, "formalization_lean/deep/w.rs": tagged})
                self.assertEqual(got, [], f"main.rs {main!r}")

    def test_inline_mod_block_resolves_children_under_its_name(self) -> None:
        """The unreached tagged files of a tree whose root `formalization_lean/main.rs` holds each row's text and
        whose one tagged file sits at each row's location. The `inline` rows pin the locations rustc 1.100.0
        accepts for `#[path = "x.rs"] mod b;` and `mod c;` inside `mod a { … }` in that root file,
        `a/x.rs` and `a/c.rs`, as reached, and the locations it rejects, `x.rs` and `c.rs`, as unreached."""
        tagged = TAG + "#[test]\nfn w() {}\n"
        inline = 'mod a {\n    #[path = "x.rs"]\n    mod b;\n    mod c;\n}\n'
        for main, where, expected in (
            (inline, "a/x.rs", []),
            (inline, "x.rs", ["formalization_lean/x.rs"]),
            (inline, "a/c.rs", []),
            (inline, "c.rs", ["formalization_lean/c.rs"]),
            ("mod outer {\n    mod w;\n}\n", "outer/w.rs", []),
            ("mod outer {\n    mod w;\n}\n", "w.rs", ["formalization_lean/w.rs"]),
            ("mod outer {\nmod w;\n}\n", "outer/w.rs", []),
            ("mod outer { mod w; }\n", "outer/w.rs", []),
            ("pub mod a {\n    mod b {\n        mod w;\n    }\n}\n", "a/b/w.rs", []),
            ("mod outer {\n    fn f() {}\n}\nmod w;\n", "w.rs", []),
            ("mod outer {\n    fn f() {}\n}\nmod w;\n", "outer/w.rs", ["formalization_lean/outer/w.rs"]),
            ("mod outer {\n    const S: &str = \"}\";\n    const C: char = '}';\n    mod w;\n}\n", "outer/w.rs", []),
            ("fn f() {\n    mod w;\n}\n", "w.rs", ["formalization_lean/w.rs"]),
            ("mod outer {\n    #[path = \"x/w.rs\"]\n    mod w;\n}\n", "outer/x/w.rs", []),
        ):
            with self.subTest(main=main, where=where):
                got = self.tree_unreached({"formalization_lean/main.rs": main, f"formalization_lean/{where}": tagged})
                self.assertEqual(got, expected, f"main.rs {main!r}, tagged file at {where}")

    def test_inline_mod_block_children_resolve_where_rustc_finds_them(self) -> None:
        """The locations `cargo build` (rustc 1.100.0) accepts for `#[path = "x.rs"] mod b;` and `mod c;` inside
        `mod a { … }`, declared in `foo.rs` reached by `mod foo;` and in `q/foo.rs` reached by
        `#[path = "q/foo.rs"] mod p;`; each other location listed is one it rejects."""
        tagged = TAG + "#[test]\nfn w() {}\n"
        inline = 'mod a {\n    #[path = "x.rs"]\n    mod b;\n    mod c;\n}\n'
        roots = {
            "foo.rs": {"main.rs": "mod foo;\n", "foo.rs": inline},
            "#[path] q/foo.rs": {"main.rs": '#[path = "q/foo.rs"]\nmod p;\n', "q/foo.rs": inline},
        }
        for declaring, where, reached in (
            ("foo.rs", "foo/a/x.rs", True),
            ("foo.rs", "x.rs", False),
            ("foo.rs", "a/x.rs", False),
            ("foo.rs", "foo/x.rs", False),
            ("foo.rs", "foo/a/c.rs", True),
            ("foo.rs", "a/c.rs", False),
            ("foo.rs", "foo/c.rs", False),
            ("#[path] q/foo.rs", "q/a/x.rs", True),
            ("#[path] q/foo.rs", "q/foo/a/x.rs", False),
            ("#[path] q/foo.rs", "q/a/c.rs", True),
            ("#[path] q/foo.rs", "q/foo/a/c.rs", False),
        ):
            with self.subTest(declaring=declaring, where=where):
                files = {f"formalization_lean/{name}": text for name, text in roots[declaring].items()}
                got = self.tree_unreached(files | {f"formalization_lean/{where}": tagged})
                expected = [] if reached else [f"formalization_lean/{where}"]
                self.assertEqual(got, expected, f"inline block in {declaring}, tagged file at {where}")

    def test_table_root_suppresses_the_auto_target_of_that_root(self) -> None:
        cargo = CARGO + '\n[[test]]\nname = "fl"\npath = "tests/formalization_lean/main.rs"\n'
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            build(root, lean=LEAN_FILE, row=ROW, test=TEST_FILE, cargo=cargo)
            targets, _ = ctm.test_targets(root, ctm.tomllib.loads(cargo))
        self.assertEqual([t.name for t in targets], ["fl"], f"targets: {targets}")

    def test_each_file_is_parsed_once_across_targets(self) -> None:
        shared = '#[path = "formalization_lean/shared.rs"] mod shared;\n'
        files = {"a.rs": shared, "b.rs": shared, "formalization_lean/shared.rs": "mod leaf;\n", "formalization_lean/leaf.rs": ""}
        parsed: list[Path] = []
        real = ctm.mod_children

        def counting(path: Path, base: Path) -> list[tuple[Path, Path]]:
            parsed.append(path)
            return real(path, base)

        with tempfile.TemporaryDirectory() as tmp, mock.patch.object(ctm, "mod_children", counting):
            root = Path(tmp)
            build(root, lean=None, row=None, test=None)
            for name, text in files.items():
                (root / "tests" / name).parent.mkdir(parents=True, exist_ok=True)
                (root / "tests" / name).write_text(text, encoding="utf-8")
            ctm.witness_target_failures(root, {(root / "tests" / "formalization_lean" / "leaf.rs").resolve()})
            counts = sorted((p.relative_to(root.resolve()).as_posix(), parsed.count(p)) for p in set(parsed))
        self.assertEqual(
            counts,
            [("tests/a.rs", 1), ("tests/b.rs", 1), ("tests/formalization_lean/leaf.rs", 1), ("tests/formalization_lean/shared.rs", 1)],
            f"parse counts per file: {counts}",
        )

    def test_table_ends_at_the_first_line_not_starting_with_a_bar(self) -> None:
        later = "\nNotes.\n\n| Lean id | Rust test | anchor |\n|---|---|---|\n| broken row |\n| CategoryTheory.Conditional.unique_as | x | y |\n"
        self.assertEqual(self.run_case(lean=LEAN_FILE, row=ROW + later, test=TEST_FILE), [])
        failures = self.run_case(lean=LEAN_FILE, row="\n" + ROW, test=TEST_FILE)
        self.assertEqual(len(failures), 1, f"a row after a blank line counted: {failures}")
        self.assertIn("no THEOREM_MAP row", failures[0])

    def test_test_false_or_harness_false_on_the_witness_target_fails(self) -> None:
        for key in ("test", "harness"):
            with self.subTest(key=key):
                table = f'[[test]]\nname = "formalization_lean"\npath = "tests/formalization_lean/main.rs"\n{key} = false\n'
                failures = self.gated_failures(CARGO + "\n" + table)
                self.assertEqual(len(failures), 1, f"failures: {failures}")
                self.assertIn(f"[[test]] `formalization_lean` holds THEOREM_MAP witnesses and has {key} = false", failures[0])

    def test_autotests_false_without_a_witness_table_fails(self) -> None:
        failures = self.run_case(lean=LEAN_FILE, row=ROW, test=TEST_FILE, cargo=CARGO + "autotests = false\n")
        got = [f.rsplit("/", 1)[-1] for f in failures]
        self.assertEqual(
            got,
            [
                "Cargo.toml: autotests = false and no [[test]] table holds the THEOREM_MAP witnesses",
                f"conditional_tests.rs: {UNREACHED}",
            ],
            f"failures: {failures}",
        )

    def test_autotests_false_with_a_witness_table_passes(self) -> None:
        cargo = CARGO + 'autotests = false\n\n[[test]]\nname = "formalization_lean"\n'
        self.assertEqual(self.run_case(lean=LEAN_FILE, row=ROW, test=TEST_FILE, cargo=cargo), [])

    def test_tagged_file_no_mod_reaches_fails(self) -> None:
        others = {"main.rs": "mod conditional_tests;\n", "orphan.rs": TAG + "#[test]\nfn orphan() {}\n"}
        failures = self.run_case(lean=LEAN_FILE, row=ROW, test=TEST_FILE, others=others)
        self.assertEqual(self.unreached(failures), [f"orphan.rs: {UNREACHED}"], f"failures: {failures}")
        self.assertEqual(len(failures), 1, f"failures: {failures}")

    def test_malformed_table_line_fails(self) -> None:
        for bad in ("| broken row |\n", "| a | b | c | d |\n", "|---|garbage\n"):
            with self.subTest(bad=bad):
                failures = self.run_case(lean=LEAN_FILE, row=ROW + bad, test=TEST_FILE)
                self.assertEqual(
                    failures, ["THEOREM_MAP.md:6: table line is not a row `| <id> | <test> | <anchor> |`"], f"{bad!r}"
                )

    def test_missing_table_header_fails(self) -> None:
        failures = self.run_case(lean=None, row=None, test=None, head="# THEOREM_MAP\n")
        self.assertEqual(failures, ["THEOREM_MAP.md: no `| Lean id` table header"])

    def main_code(self, **kw: object) -> int:
        with tempfile.TemporaryDirectory() as tmp, contextlib.redirect_stdout(io.StringIO()):
            root = Path(tmp)
            build(root, **kw)
            return ctm.main(["check_theorem_map.py", str(root)])

    def test_main_returns_1_on_a_failure(self) -> None:
        code = self.main_code(lean=LEAN_FILE, row=None, test=None)
        self.assertEqual(code, 1, f"main returned {code} on an uncovered theorem")

    def test_main_returns_0_on_a_clean_tree(self) -> None:
        code = self.main_code(lean=LEAN_FILE, row=ROW, test=TEST_FILE)
        self.assertEqual(code, 0, f"main returned {code} on a covered theorem")


if __name__ == "__main__":
    unittest.main()
