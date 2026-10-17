#!/usr/bin/env python3
"""Unit tests for print_axioms (no Lean needed)."""

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

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


def probe(*lines: str) -> pa.ProbeResult:
    return pa.parse_output("".join(f"{line}\n" for line in lines))


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
        self.assertEqual((r.modules, r.consts), (set(), []))


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

    def test_clean_probe_passes(self) -> None:
        r = probe("MODULE\tPeluang", "MODULE\tPeluang.X", "CONST\tPeluang.a\tPeluang.X\ttrue\t-\tpropext")
        self.assertEqual(pa.evaluate(r, ["Peluang", "Peluang.X"], ["Peluang.a"], {"Peluang.a"}), [])


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


if __name__ == "__main__":
    unittest.main()
