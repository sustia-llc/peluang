#!/usr/bin/env python3
"""Unit tests for print_axioms (no Lean needed)."""

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import print_axioms as pa  # noqa: E402

NAMES = ["Peluang.a", "Peluang.b"]


class ParseOutput(unittest.TestCase):
    def test_allowed_axioms_pass(self) -> None:
        out = (
            "'Peluang.a' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
            "'Peluang.b' does not depend on any axioms\n"
        )
        self.assertEqual(pa.parse_output(NAMES, out), [])

    def test_sorry_fails(self) -> None:
        out = (
            "'Peluang.a' depends on axioms: [propext, sorryAx]\n"
            "'Peluang.b' does not depend on any axioms\n"
        )
        failures = pa.parse_output(NAMES, out)
        self.assertEqual(len(failures), 1, failures)
        self.assertIn("Peluang.a", failures[0])
        self.assertIn("sorryAx", failures[0])

    def test_native_decide_axiom_fails(self) -> None:
        out = (
            "'Peluang.a' depends on axioms: [Lean.ofReduceBool]\n"
            "'Peluang.b' does not depend on any axioms\n"
        )
        failures = pa.parse_output(NAMES, out)
        self.assertEqual(len(failures), 1, failures)
        self.assertIn("Lean.ofReduceBool", failures[0])

    def test_wrapped_axiom_list_passes(self) -> None:
        out = (
            "'Peluang.a' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n"
            "'Peluang.b' does not depend on any axioms\n"
        )
        self.assertEqual(pa.parse_output(NAMES, out), [])

    def test_wrapped_axiom_list_with_sorry_fails(self) -> None:
        out = (
            "'Peluang.a' depends on axioms: [propext,\n Classical.choice,\n sorryAx]\n"
            "'Peluang.b' does not depend on any axioms\n"
        )
        failures = pa.parse_output(NAMES, out)
        self.assertEqual(len(failures), 1, failures)
        self.assertIn("sorryAx", failures[0])

    def test_primed_name_parses(self) -> None:
        out = "'Peluang.a'' depends on axioms: [sorryAx]\n"
        failures = pa.parse_output(["Peluang.a'"], out)
        self.assertEqual(len(failures), 1, failures)
        self.assertIn("sorryAx", failures[0])

    def test_private_name_is_unmangled(self) -> None:
        out = "'_private.Peluang.X.0.Peluang.a' depends on axioms: [sorryAx]\n"
        failures = pa.parse_output(["Peluang.a"], out)
        self.assertEqual(len(failures), 1, failures)
        self.assertIn("sorryAx", failures[0])

    def test_missing_result_fails(self) -> None:
        out = "'Peluang.a' does not depend on any axioms\n"
        failures = pa.parse_output(NAMES, out)
        self.assertEqual(failures, ["`Peluang.b`: no `#print axioms` result"])

    def test_empty_name_list_passes(self) -> None:
        self.assertEqual(pa.parse_output([], ""), [])


class Evaluate(unittest.TestCase):
    def test_nonzero_exit_reports_only_lean_error(self) -> None:
        failures = pa.evaluate(NAMES, 1, "Probe.lean:3:0: error: unknown module\n")
        self.assertEqual(len(failures), 1, failures)
        self.assertIn("lean exited 1", failures[0])
        self.assertIn("unknown module", failures[0])


class ProbeSource(unittest.TestCase):
    def test_module_with_import_all_and_one_print_per_name(self) -> None:
        src = pa.probe_source(["Peluang", "Peluang.X"], NAMES)
        self.assertTrue(src.startswith("module\n"))
        self.assertIn("import all Peluang\n", src)
        self.assertIn("import all Peluang.X\n", src)
        self.assertEqual(src.count("#print axioms "), len(NAMES))

    def test_module_names_from_tree(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            lean = Path(tmp)
            (lean / "Peluang" / "Markov").mkdir(parents=True)
            (lean / "Peluang" / "Markov" / "Derived.lean").write_text("", encoding="utf-8")
            (lean / "Peluang" / "AlmostSure.lean").write_text("", encoding="utf-8")
            self.assertEqual(pa.module_names(lean), ["Peluang", "Peluang.AlmostSure", "Peluang.Markov.Derived"])

    def test_module_names_without_library_dir(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            self.assertEqual(pa.module_names(Path(tmp)), ["Peluang"])


if __name__ == "__main__":
    unittest.main()
