#!/usr/bin/env python3
"""Unit tests for probe_selftest (no Lean needed)."""

from __future__ import annotations

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import probe_selftest as ps  # noqa: E402

ROOT_SOURCE = "module\n\npublic import Peluang.Markov.Derived\n"


class FakeLake:
    def __init__(self, returncode: int) -> None:
        self.returncode = returncode
        self.calls: list[list[str]] = []

    def __call__(
        self, args: list[str], lean_dir: Path, env: dict[str, str] | None = None
    ) -> subprocess.CompletedProcess[str]:
        self.calls.append(args)
        return subprocess.CompletedProcess(["lake", *args], self.returncode, "out", "err")


class Build(unittest.TestCase):
    def test_builds_the_peluang_target(self) -> None:
        lake = FakeLake(0)
        with mock.patch.object(ps.pa, "run_lake", lake):
            failures = ps.build(Path("lean"), "x")
        self.assertEqual(lake.calls, [["build", "Peluang"]], f"lake calls were {lake.calls}")
        self.assertEqual(failures, [], f"failures: {failures}")

    def test_failed_build_is_reported(self) -> None:
        with mock.patch.object(ps.pa, "run_lake", FakeLake(1)):
            failures = ps.build(Path("lean"), "x")
        self.assertEqual(failures, ["lake build (x) failed (1):\nouterr"], f"failures: {failures}")


class Run(unittest.TestCase):
    def test_builds_linter_then_peluang_twice_and_restores_the_tree(self) -> None:
        lake = FakeLake(0)
        with tempfile.TemporaryDirectory() as tmp:
            lean = Path(tmp) / "lean"
            lean.mkdir()
            root_file = lean / "Peluang.lean"
            root_file.write_text(ROOT_SOURCE, encoding="utf-8")
            with mock.patch.object(ps.pa, "run_lake", lake), mock.patch.object(ps.pa, "check", return_value=(0, [])):
                ps.run(Path(tmp))
            restored = root_file.read_text(encoding="utf-8")
            leftovers = sorted(p.name for p in lean.iterdir())
        self.assertEqual(
            lake.calls, [["build", "PeluangLint"], ["build", "Peluang"], ["build", "Peluang"]], f"lake calls were {lake.calls}"
        )
        self.assertEqual(restored, ROOT_SOURCE, f"lean/Peluang.lean after run: {restored!r}")
        self.assertEqual(leftovers, ["Peluang.lean"], f"lean/ after run: {leftovers}")


if __name__ == "__main__":
    unittest.main()
