#!/usr/bin/env python3
"""Unit tests for print_axioms.parse_output and probe_source (no Lean needed)."""

from __future__ import annotations

import sys
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

    def test_missing_result_fails(self) -> None:
        out = "'Peluang.a' does not depend on any axioms\n"
        failures = pa.parse_output(NAMES, out)
        self.assertEqual(failures, ["`Peluang.b`: no `#print axioms` result"])

    def test_empty_name_list_passes(self) -> None:
        self.assertEqual(pa.parse_output([], ""), [])


class ProbeSource(unittest.TestCase):
    def test_one_print_per_name(self) -> None:
        src = pa.probe_source(NAMES)
        self.assertTrue(src.startswith("import Peluang\n"))
        self.assertEqual(src.count("#print axioms "), len(NAMES))
        self.assertIn("#print axioms Peluang.b\n", src)


if __name__ == "__main__":
    unittest.main()
