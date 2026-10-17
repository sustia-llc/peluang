#!/usr/bin/env python3
"""Unit tests for print_axioms (no Lean needed)."""

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import print_axioms as pa  # noqa: E402

OUTPUT = (
    "MODULE\tPeluang\n"
    "MODULE\tPeluang.X\n"
    "AXIOMS\tPeluang.a\tpropext,Classical.choice,Quot.sound\n"
    "AXIOMS\t_private.Peluang.X.0.Peluang.b\t\n"
    "AXIOMS\tPeluang.instFoo\tsorryAx\n"
)


class ParseOutput(unittest.TestCase):
    def test_modules_and_axioms(self) -> None:
        r = pa.parse_output(OUTPUT)
        self.assertEqual(r.modules, {"Peluang", "Peluang.X"})
        self.assertEqual(r.axioms["Peluang.a"], ["propext", "Classical.choice", "Quot.sound"])
        self.assertEqual(r.axioms["_private.Peluang.X.0.Peluang.b"], [])
        self.assertEqual(r.axioms["Peluang.instFoo"], ["sorryAx"])

    def test_unrelated_lines_ignored(self) -> None:
        r = pa.parse_output("warning: something\nAXIOMS\tonly-two-fields\n")
        self.assertEqual((r.modules, r.axioms), (set(), {}))


class Evaluate(unittest.TestCase):
    def test_disallowed_axiom_fails_with_display_name(self) -> None:
        failures = pa.evaluate(pa.parse_output(OUTPUT), ["Peluang.X"], [])
        self.assertEqual(len(failures), 1, failures)
        self.assertIn("`Peluang.instFoo`: depends on sorryAx", failures[0])

    def test_private_sorry_reported_unmangled(self) -> None:
        out = "MODULE\tPeluang.X\nAXIOMS\t_private.Peluang.X.0.Peluang.h\tsorryAx\n"
        failures = pa.evaluate(pa.parse_output(out), ["Peluang.X"], [])
        self.assertEqual(failures, ["`Peluang.h`: depends on sorryAx (allowed: Classical.choice, Quot.sound, propext)"])

    def test_native_decide_axiom_fails(self) -> None:
        out = "MODULE\tPeluang.X\nAXIOMS\tPeluang.d\tLean.ofReduceBool\n"
        failures = pa.evaluate(pa.parse_output(out), ["Peluang.X"], [])
        self.assertEqual(len(failures), 1, failures)
        self.assertIn("Lean.ofReduceBool", failures[0])

    def test_orphan_module_fails(self) -> None:
        out = "MODULE\tPeluang\nAXIOMS\tPeluang.a\t\n"
        failures = pa.evaluate(pa.parse_output(out), ["Peluang.Orphan"], [])
        self.assertEqual(len(failures), 1, failures)
        self.assertIn("`Peluang.Orphan`: file under lean/Peluang/ is not imported", failures[0])

    def test_scanned_name_missing_from_environment_fails(self) -> None:
        out = "MODULE\tPeluang.X\nAXIOMS\tPeluang.a\t\n"
        failures = pa.evaluate(pa.parse_output(out), ["Peluang.X"], ["Peluang.a", "Peluang.ghost"])
        self.assertEqual(len(failures), 1, failures)
        self.assertIn("`Peluang.ghost`: scanned as a theorem", failures[0])

    def test_scanned_private_name_matches(self) -> None:
        out = "MODULE\tPeluang.X\nAXIOMS\t_private.Peluang.X.0.Peluang.p\t\n"
        self.assertEqual(pa.evaluate(pa.parse_output(out), ["Peluang.X"], ["Peluang.p"]), [])

    def test_clean_probe_passes(self) -> None:
        out = "MODULE\tPeluang\nMODULE\tPeluang.X\nAXIOMS\tPeluang.a\tpropext\n"
        self.assertEqual(pa.evaluate(pa.parse_output(out), ["Peluang.X"], ["Peluang.a"]), [])


class ModuleNames(unittest.TestCase):
    def test_module_names_from_tree(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            lean = Path(tmp)
            (lean / "Peluang" / "Markov").mkdir(parents=True)
            (lean / "Peluang" / "Markov" / "Derived.lean").write_text("", encoding="utf-8")
            (lean / "Peluang" / "AlmostSure.lean").write_text("", encoding="utf-8")
            self.assertEqual(pa.module_names(lean), ["Peluang.AlmostSure", "Peluang.Markov.Derived"])

    def test_no_library_dir_skips_probe(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            (Path(tmp) / "lean").mkdir()
            self.assertEqual(pa.check(Path(tmp)), (0, []))


if __name__ == "__main__":
    unittest.main()
