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
LEAN_FILE = "namespace Peluang.Conditional\n\ntheorem unique_as : True := trivial\n\nend Peluang.Conditional\n"
TEST_FILE = "/// THEOREM_MAP: Peluang.Conditional.unique_as\n#[test]\nfn unique_as() {}\n"


def build(root: Path, *, lean: str | None, row: str | None, test: str | None) -> None:
    (root / "THEOREM_MAP.md").write_text(MAP_HEAD + (row or ""), encoding="utf-8")
    if lean is not None:
        d = root / "lean" / "Peluang"
        d.mkdir(parents=True)
        (d / "Conditional.lean").write_text(lean, encoding="utf-8")
    if test is not None:
        d = root / "tests" / "formalization_lean"
        d.mkdir(parents=True)
        (d / "conditional_tests.rs").write_text(test, encoding="utf-8")


class CheckTheoremMap(unittest.TestCase):
    def run_case(self, **kw: str | None) -> list[str]:
        with tempfile.TemporaryDirectory() as tmp:
            build(Path(tmp), **kw)
            return ctm.check(Path(tmp))

    def test_empty_repo_passes(self) -> None:
        self.assertEqual(self.run_case(lean=None, row=None, test=None), [])

    def test_covered_theorem_passes(self) -> None:
        row = "| Peluang.Conditional.unique_as | tests/formalization_lean/conditional_tests.rs::unique_as | Fritz 2020 Prop. 13.7 |\n"
        self.assertEqual(self.run_case(lean=LEAN_FILE, row=row, test=TEST_FILE), [])

    def test_uncovered_theorem_fails(self) -> None:
        failures = self.run_case(lean=LEAN_FILE, row=None, test=None)
        self.assertEqual(len(failures), 1, failures)
        self.assertIn("Peluang.Conditional.unique_as", failures[0])
        self.assertIn("no THEOREM_MAP row", failures[0])

    def test_opt_out_passes(self) -> None:
        lean = LEAN_FILE.replace("theorem unique_as", "-- WITNESS: none (helper lemma)\ntheorem unique_as")
        self.assertEqual(self.run_case(lean=lean, row=None, test=None), [])

    def test_row_without_test_file_fails(self) -> None:
        row = "| Peluang.Conditional.unique_as | tests/formalization_lean/conditional_tests.rs::unique_as | — |\n"
        failures = self.run_case(lean=LEAN_FILE, row=row, test=None)
        self.assertEqual(len(failures), 1, failures)
        self.assertIn("does not exist", failures[0])

    def test_row_without_tag_fails(self) -> None:
        row = "| Peluang.Conditional.unique_as | tests/formalization_lean/conditional_tests.rs::unique_as | — |\n"
        failures = self.run_case(lean=LEAN_FILE, row=row, test="#[test]\nfn unique_as() {}\n")
        self.assertEqual(len(failures), 1, failures)
        self.assertIn("carries 0", failures[0])

    def test_tag_on_wrong_fn_fails(self) -> None:
        row = "| Peluang.Conditional.unique_as | tests/formalization_lean/conditional_tests.rs::unique_as | — |\n"
        test = TEST_FILE.replace("fn unique_as", "fn other_name")
        failures = self.run_case(lean=LEAN_FILE, row=row, test=test)
        self.assertEqual(len(failures), 1, failures)
        self.assertIn("row names `unique_as`", failures[0])

    def test_duplicate_tag_fails(self) -> None:
        row = "| Peluang.Conditional.unique_as | tests/formalization_lean/conditional_tests.rs::unique_as | — |\n"
        failures = self.run_case(lean=LEAN_FILE, row=row, test=TEST_FILE + TEST_FILE.replace("fn unique_as", "fn again"))
        self.assertEqual(len(failures), 1, failures)
        self.assertIn("carries 2", failures[0])

    def test_mathlib_row_is_optional(self) -> None:
        row = "| mathlib:CategoryTheory.MarkovCategory.eq_discard | — | — |\n"
        self.assertEqual(self.run_case(lean=None, row=row, test=None), [])

    def test_section_end_keeps_namespace(self) -> None:
        lean = "namespace Peluang.Conditional\n\nsection\nvariable (n : Nat)\nend\n\ntheorem unique_as : True := trivial\n\nend Peluang.Conditional\n"
        row = "| Peluang.Conditional.unique_as | tests/formalization_lean/conditional_tests.rs::unique_as | — |\n"
        self.assertEqual(self.run_case(lean=lean, row=row, test=TEST_FILE), [])

    def test_named_section_end_pops_section_only(self) -> None:
        lean = "namespace A\nsection S\nend S\nend A\n\nnamespace Peluang.Conditional\ntheorem unique_as : True := trivial\nend Peluang.Conditional\n"
        row = "| Peluang.Conditional.unique_as | tests/formalization_lean/conditional_tests.rs::unique_as | — |\n"
        self.assertEqual(self.run_case(lean=lean, row=row, test=TEST_FILE), [])

    def test_multiline_theorem_header_detected(self) -> None:
        lean = "namespace Peluang.Conditional\n\n@[simp]\ntheorem\n  unique_as : True := trivial\n\nend Peluang.Conditional\n"
        failures = self.run_case(lean=lean, row=None, test=None)
        self.assertEqual(len(failures), 1, failures)
        self.assertIn("Peluang.Conditional.unique_as", failures[0])

    def test_opt_out_above_attribute_passes(self) -> None:
        lean = LEAN_FILE.replace("theorem unique_as", "-- WITNESS: none (helper)\n@[simp]\ntheorem unique_as")
        self.assertEqual(self.run_case(lean=lean, row=None, test=None), [])

    def test_duplicate_row_fails(self) -> None:
        row = (
            "| Peluang.Conditional.unique_as | tests/formalization_lean/conditional_tests.rs::unique_as | — |\n"
            "| Peluang.Conditional.unique_as | tests/formalization_lean/other.rs::unique_as | — |\n"
        )
        failures = self.run_case(lean=LEAN_FILE, row=row, test=TEST_FILE)
        self.assertEqual(len(failures), 1, failures)
        self.assertIn("duplicate row", failures[0])

    def test_public_section_end_keeps_namespace(self) -> None:
        for header in ("public section", "@[expose] public section", "public noncomputable section"):
            with self.subTest(header=header):
                lean = f"namespace Peluang\n{header}\ntheorem t1 : True := trivial\nend\ntheorem t2 : True := trivial\nend Peluang\n"
                with tempfile.TemporaryDirectory() as tmp:
                    d = Path(tmp) / "Peluang"
                    d.mkdir()
                    (d / "X.lean").write_text(lean, encoding="utf-8")
                    names = [x.qualified for x in ctm.lean_decls(d)]
                self.assertEqual(names, ["Peluang.t1", "Peluang.t2"], f"header {header!r} gave {names}")

    def test_visibility_modifiers_detected(self) -> None:
        lean = "namespace Peluang\npublic theorem a : True := trivial\nprivate theorem b : True := trivial\n@[simp] public theorem c : True := trivial\nend Peluang\n"
        with tempfile.TemporaryDirectory() as tmp:
            d = Path(tmp) / "Peluang"
            d.mkdir()
            (d / "X.lean").write_text(lean, encoding="utf-8")
            names = [x.qualified for x in ctm.lean_decls(d)]
        self.assertEqual(names, ["Peluang.a", "Peluang.b", "Peluang.c"], f"got {names}")

    def names_in(self, lean: str) -> list[str]:
        with tempfile.TemporaryDirectory() as tmp:
            d = Path(tmp) / "Peluang"
            d.mkdir()
            (d / "X.lean").write_text(lean, encoding="utf-8")
            return [x.qualified for x in ctm.lean_decls(d)]

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
        with tempfile.TemporaryDirectory() as tmp:
            d = Path(tmp) / "Peluang"
            d.mkdir()
            (d / "X.lean").write_text(lean, encoding="utf-8")
            decls = ctm.lean_decls(d)
        self.assertEqual([(x.qualified, x.opted_out) for x in decls], [("Peluang.h", True)])

    def test_bad_test_column_fails(self) -> None:
        row = "| Peluang.Conditional.unique_as | conditional_tests.rs::unique_as | — |\n"
        failures = self.run_case(lean=LEAN_FILE, row=row, test=TEST_FILE)
        self.assertEqual(len(failures), 1, failures)
        self.assertIn("is not `tests/formalization_lean/", failures[0])


if __name__ == "__main__":
    unittest.main()
