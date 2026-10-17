#!/usr/bin/env python3
"""Unit tests for check_lean_source (no Lean needed)."""

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_lean_source as cls  # noqa: E402


class Scan(unittest.TestCase):
    def test_sorry_term_hits(self) -> None:
        self.assertEqual(cls.scan("theorem t : False := sorry\n"), [(1, "sorry")])

    def test_sorry_tactic_hits(self) -> None:
        self.assertEqual(cls.scan("theorem t : False := by\n  sorry\n"), [(2, "sorry")])

    def test_axiom_declaration_hits(self) -> None:
        src = "axiom a : False\n  private axiom b : False\n@[simp] axiom c : False\n"
        self.assertEqual(cls.scan(src), [(1, "axiom declaration"), (2, "axiom declaration"), (3, "axiom declaration")])

    def test_line_comment_ignored(self) -> None:
        self.assertEqual(cls.scan("-- no sorry here; axiom-free\ntheorem t : True := trivial -- sorry\n"), [])

    def test_docstring_ignored(self) -> None:
        self.assertEqual(cls.scan("/-- Proved with zero sorry.\naxiom-free. -/\ntheorem t : True := trivial\n"), [])

    def test_nested_block_comment_ignored(self) -> None:
        src = "/- outer /- inner sorry -/ still comment sorry -/\ntheorem t : False := sorry\n"
        self.assertEqual(cls.scan(src), [(2, "sorry")])

    def test_string_literal_ignored(self) -> None:
        self.assertEqual(cls.scan('def s : String := "sorry -- \\" /- not a comment"\n'), [])

    def test_code_after_string_with_dashes_scanned(self) -> None:
        self.assertEqual(cls.scan('def s : String := "--"\ntheorem t : False := sorry\n'), [(2, "sorry")])

    def test_identifier_containing_sorry_ignored(self) -> None:
        self.assertEqual(cls.scan("theorem sorryFree : True := trivial\ntheorem t : True := Foo.sorry'\n"), [])

    def test_axiom_word_inside_name_ignored(self) -> None:
        self.assertEqual(cls.scan("theorem axiom_free : True := trivial\n"), [])

    def test_char_literal_quote_does_not_open_string(self) -> None:
        self.assertEqual(cls.scan("def q : Char := '\"'\ntheorem t : False := sorry\n"), [(2, "sorry")])

    def test_char_literal_escape_does_not_open_string(self) -> None:
        self.assertEqual(cls.scan("def q : Char := '\\''\ntheorem t : False := sorry\n"), [(2, "sorry")])

    def test_primed_name_is_not_char_literal(self) -> None:
        self.assertEqual(cls.scan("theorem a' : True := trivial\ntheorem b' : False := sorry\n"), [(2, "sorry")])

    def test_raw_string_ignored_and_closes(self) -> None:
        src = 'def s := r"sorry \\"\ntheorem t : False := sorry\ndef u := r#"has " sorry"#\n'
        self.assertEqual(cls.scan(src), [(2, "sorry")])

    def test_identifier_ending_in_r_is_not_raw_string(self) -> None:
        self.assertEqual(cls.scan('def s := for"x"\ntheorem t : False := sorry\n'), [(2, "sorry")])

    def test_line_numbers_survive_block_comments(self) -> None:
        self.assertEqual(cls.scan("/-\n\n\n-/\nexample : False := sorry\n"), [(5, "sorry")])


class Check(unittest.TestCase):
    def test_skips_lake_dir(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "lean" / ".lake" / "packages").mkdir(parents=True)
            (root / "lean" / ".lake" / "packages" / "X.lean").write_text("example : False := sorry\n", encoding="utf-8")
            (root / "lean" / "Peluang.lean").write_text("-- root\n", encoding="utf-8")
            self.assertEqual(cls.check(root), [])

    def test_reports_path_and_line(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "lean" / "Peluang").mkdir(parents=True)
            (root / "lean" / "Peluang" / "A.lean").write_text("\ntheorem t : False := sorry\n", encoding="utf-8")
            self.assertEqual(cls.check(root), ["lean/Peluang/A.lean:2: sorry"])


if __name__ == "__main__":
    unittest.main()
