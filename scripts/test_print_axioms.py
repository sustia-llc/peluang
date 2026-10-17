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
    "CONST\tPeluang.a\ttrue\tpropext,Classical.choice,Quot.sound\n"
    "CONST\t_private.Peluang.X.0.Peluang.b\ttrue\t\n"
    "CONST\tPeluang.instFoo\tfalse\tsorryAx\n"
    "CONST\tPeluang.X.«odd name»\ttrue\t\n"
)


def probe(*lines: str) -> pa.ProbeResult:
    return pa.parse_output("".join(f"{line}\n" for line in lines))


class ParseOutput(unittest.TestCase):
    def test_modules_axioms_and_source_theorems(self) -> None:
        r = pa.parse_output(OUTPUT)
        self.assertEqual(r.modules, {"Peluang", "Peluang.X"})
        self.assertEqual(r.axioms["Peluang.a"], ["propext", "Classical.choice", "Quot.sound"])
        self.assertEqual(r.axioms["Peluang.instFoo"], ["sorryAx"])
        self.assertEqual(r.source_theorems, {"Peluang.a", "Peluang.b", "Peluang.X.odd name"})

    def test_unrelated_lines_ignored(self) -> None:
        r = pa.parse_output("warning: something\nCONST\tonly\tthree\n")
        self.assertEqual((r.modules, r.axioms, r.source_theorems), (set(), {}, set()))


class Evaluate(unittest.TestCase):
    def test_disallowed_axiom_fails_with_display_name(self) -> None:
        failures = pa.evaluate(pa.parse_output(OUTPUT), ["Peluang", "Peluang.X"], ["Peluang.a", "Peluang.b", "Peluang.X.odd name"])
        self.assertEqual(failures, ["`Peluang.instFoo`: depends on sorryAx (allowed: Classical.choice, Quot.sound, propext)"])

    def test_private_sorry_reported_unmangled(self) -> None:
        r = probe("MODULE\tPeluang", "CONST\t_private.Peluang.0.Peluang.h\ttrue\tsorryAx")
        failures = pa.evaluate(r, ["Peluang"], ["Peluang.h"])
        self.assertEqual(failures, ["`Peluang.h`: depends on sorryAx (allowed: Classical.choice, Quot.sound, propext)"])

    def test_native_decide_axiom_fails(self) -> None:
        r = probe("MODULE\tPeluang", "CONST\tPeluang.d\tfalse\tPeluang.d._native.native_decide.ax_1_1")
        failures = pa.evaluate(r, ["Peluang"], [])
        self.assertEqual(len(failures), 1, failures)
        self.assertIn("native_decide", failures[0])

    def test_orphan_module_fails(self) -> None:
        r = probe("MODULE\tPeluang")
        failures = pa.evaluate(r, ["Peluang", "Peluang.Orphan"], [])
        self.assertEqual(failures, ["`Peluang.Orphan`: library file is not imported (transitively) by lean/Peluang.lean"])

    def test_scanned_name_missing_from_environment_fails(self) -> None:
        r = probe("MODULE\tPeluang", "CONST\tPeluang.a\ttrue\t")
        failures = pa.evaluate(r, ["Peluang"], ["Peluang.a", "Peluang.ghost"])
        self.assertEqual(len(failures), 1, failures)
        self.assertIn("`Peluang.ghost`: scanned as a theorem", failures[0])

    def test_source_theorem_missed_by_scanner_fails(self) -> None:
        r = probe("MODULE\tPeluang", "CONST\tPeluang.a\ttrue\t", "CONST\tPeluang.missed\ttrue\t")
        failures = pa.evaluate(r, ["Peluang"], ["Peluang.a"])
        self.assertEqual(failures, ["`Peluang.missed`: source theorem of the library that check_theorem_map does not scan"])

    def test_generated_theorem_not_required_in_scan(self) -> None:
        r = probe("MODULE\tPeluang", "CONST\tPeluang.Box.mk.inj\tfalse\t")
        self.assertEqual(pa.evaluate(r, ["Peluang"], []), [])

    def test_clean_probe_passes(self) -> None:
        r = probe("MODULE\tPeluang", "MODULE\tPeluang.X", "CONST\tPeluang.a\ttrue\tpropext")
        self.assertEqual(pa.evaluate(r, ["Peluang", "Peluang.X"], ["Peluang.a"]), [])


class ModuleNames(unittest.TestCase):
    def test_root_and_tree(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            lean = Path(tmp)
            (lean / "Peluang" / "Markov").mkdir(parents=True)
            (lean / "Peluang" / "Markov" / "Derived.lean").write_text("", encoding="utf-8")
            (lean / "Peluang" / "AlmostSure.lean").write_text("", encoding="utf-8")
            self.assertEqual(pa.module_names(lean), ["Peluang", "Peluang.AlmostSure", "Peluang.Markov.Derived"])

    def test_without_library_dir(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            self.assertEqual(pa.module_names(Path(tmp)), ["Peluang"])


if __name__ == "__main__":
    unittest.main()
