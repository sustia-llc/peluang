#!/usr/bin/env python3
"""Unit tests for check_lake_log (no Lean needed)."""

from __future__ import annotations

import contextlib
import io
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_lake_log as cll  # noqa: E402

OK = "check_lake_log: ok (1 audit line, 0 warning lines)\n"

AUDIT = "info: PeluangTest/Audit.lean:19:0: peluangTest audit: 38 files, 37 imported PeluangTest modules\n"

CLEAN_BUILD = """\
✔ [4342/4355] Built Peluang.Independence.Composition (2.3s)
✔ [4347/4355] Built PeluangTest.Independence.Composition (1.3s)
ℹ [4351/4355] Built PeluangTest.Lint (2.4s)
info: PeluangTest/Lint.lean:16:0: -- Found 0 errors in 336 declarations (plus 179 automatically generated ones) in Peluang with 15 linters


-- All linting checks passed!
ℹ [4353/4355] Built PeluangTest.Audit (1.4s)
info: PeluangTest/Audit.lean:19:0: peluangTest audit: 38 files, 37 imported PeluangTest modules
Build completed successfully (4355 jobs).
"""

WARNING_BUILD = """\
⚠ [4342/4355] Built Peluang.Independence.Composition (2.3s)
warning: Peluang/Independence/Composition.lean:15:9: Variable name `x` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _x

Note: This linter can be disabled with `set_option linter.unusedVariables false`
ℹ [4351/4355] Built PeluangTest.Lint (2.4s)
info: PeluangTest/Lint.lean:16:0: -- Found 0 errors in 336 declarations (plus 179 automatically generated ones) in Peluang with 15 linters


-- All linting checks passed!
ℹ [4353/4355] Built PeluangTest.Audit (1.4s)
info: PeluangTest/Audit.lean:19:0: peluangTest audit: 38 files, 37 imported PeluangTest modules
Build completed successfully (4355 jobs).
"""

NO_AUDIT_BUILD = """\
✔ [4342/4355] Built Peluang.Independence.Composition (2.3s)
ℹ [4351/4355] Built PeluangTest.Lint (2.4s)
info: PeluangTest/Lint.lean:16:0: -- Found 0 errors in 336 declarations (plus 179 automatically generated ones) in Peluang with 15 linters


-- All linting checks passed!
✔ [4353/4355] Built PeluangTest.Audit (1.4s)
Build completed successfully (4355 jobs).
"""


def run(content: str | bytes) -> tuple[int, str]:
    """The exit code and stdout of `main` on a log file that holds `content`, with the path of that file
    replaced by `LOG` in stdout."""
    data = content.encode("utf-8") if isinstance(content, str) else content
    out = io.StringIO()
    with tempfile.TemporaryDirectory() as tmp:
        log = Path(tmp) / "lake-build.log"
        log.write_bytes(data)
        with contextlib.redirect_stdout(out):
            code = cll.main(["check_lake_log.py", str(log)])
    return code, out.getvalue().replace(str(log), "LOG")


class Main(unittest.TestCase):
    def assert_run(self, content: str | bytes, expected: tuple[int, str]) -> None:
        got = run(content)
        self.assertEqual(got, expected, f"expected {expected!r}, observed {got!r}")

    def test_clean_log_passes_with_the_ok_line(self) -> None:
        self.assert_run("Built Peluang\n" + AUDIT + "Build completed successfully (4355 jobs).\n", (0, OK))

    def test_one_warning_line_fails_and_names_its_line_number(self) -> None:
        expected = "LOG:2: warning: unused variable\ncheck_lake_log: 1 failure(s)\n"
        self.assert_run("Built Peluang\nwarning: unused variable\n" + AUDIT, (1, expected))

    def test_warning_line_and_missing_audit_line_give_both_failures(self) -> None:
        expected = (
            "LOG:1: warning: unused variable\n"
            "LOG: 0 audit line(s), expected exactly 1\n"
            "check_lake_log: 2 failure(s)\n"
        )
        self.assert_run("warning: unused variable\nBuild completed successfully (4355 jobs).\n", (1, expected))

    def test_zero_audit_lines_fail(self) -> None:
        expected = "LOG: 0 audit line(s), expected exactly 1\ncheck_lake_log: 1 failure(s)\n"
        self.assert_run("Built Peluang\nBuild completed successfully (4355 jobs).\n", (1, expected))

    def test_two_audit_lines_fail(self) -> None:
        expected = "LOG: 2 audit line(s), expected exactly 1\ncheck_lake_log: 1 failure(s)\n"
        self.assert_run(AUDIT + "Built Peluang\n" + AUDIT, (1, expected))

    def test_warning_inside_a_longer_line_fails(self) -> None:
        line = "warning: Peluang.lean:15:9: Variable name `x` is not explicitly referenced."
        for content, lineno in ((AUDIT + line + "\n", 2), (AUDIT + "\n\n  lake: " + line + " (1)\n", 4)):
            with self.subTest(content=content):
                shown = content.split("\n")[lineno - 1]
                self.assert_run(content, (1, f"LOG:{lineno}: {shown}\ncheck_lake_log: 1 failure(s)\n"))

    def test_audit_like_lines_that_do_not_match_are_not_counted(self) -> None:
        expected = "LOG: 0 audit line(s), expected exactly 1\ncheck_lake_log: 1 failure(s)\n"
        for line in (
            "peluangTest audit: x files",
            "peluangTest audit:  38 files",
            "peluangTest audit: files",
            "peluangTest audit: 38 file",
            "peluangtest audit: 38 files",
            "error: PeluangTest/Audit.lean:19:0: peluangTest audit: A does not import B",
        ):
            with self.subTest(line=line):
                self.assert_run(line + "\n", (1, expected))
                self.assert_run(line + "\n" + AUDIT, (0, OK))

    def test_empty_log_fails_with_zero_audit_lines(self) -> None:
        self.assert_run("", (1, "LOG: 0 audit line(s), expected exactly 1\ncheck_lake_log: 1 failure(s)\n"))

    def test_undecodable_bytes_are_replaced(self) -> None:
        self.assert_run(b"\xff\xfe Built\n" + AUDIT.encode("utf-8"), (0, OK))
        expected = "LOG:1: � warning: x\ncheck_lake_log: 1 failure(s)\n"
        self.assert_run(b"\xff warning: x\n" + AUDIT.encode("utf-8"), (1, expected))

    def test_missing_file_fails(self) -> None:
        out = io.StringIO()
        with tempfile.TemporaryDirectory() as tmp, contextlib.redirect_stdout(out):
            log = Path(tmp) / "absent.log"
            code = cll.main(["check_lake_log.py", str(log)])
        got = (code, out.getvalue().replace(str(log), "LOG"))
        expected = (1, "LOG: missing\ncheck_lake_log: 1 failure(s)\n")
        self.assertEqual(got, expected, f"expected {expected!r}, observed {got!r}")

    def test_directory_is_not_readable(self) -> None:
        out = io.StringIO()
        with tempfile.TemporaryDirectory() as tmp, contextlib.redirect_stdout(out):
            code = cll.main(["check_lake_log.py", tmp])
        got = (code, out.getvalue().replace(tmp, "LOG"))
        expected = (1, "LOG: not readable: Is a directory\ncheck_lake_log: 1 failure(s)\n")
        self.assertEqual(got, expected, f"expected {expected!r}, observed {got!r}")

    def test_wrong_argument_count_exits_2_with_the_usage_line(self) -> None:
        for argv in (["check_lake_log.py"], ["check_lake_log.py", "a.log", "b.log"]):
            with self.subTest(argv=argv):
                out, err = io.StringIO(), io.StringIO()
                with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
                    code = cll.main(argv)
                got = (code, out.getvalue(), err.getvalue())
                expected = (2, "", "Usage: check_lake_log.py LOG\n")
                self.assertEqual(got, expected, f"expected {expected!r}, observed {got!r}")


class BuildLogs(unittest.TestCase):
    def assert_run(self, content: str, expected: tuple[int, str]) -> None:
        got = run(content)
        self.assertEqual(got, expected, f"expected {expected!r}, observed {got!r}")

    def test_clean_build_passes(self) -> None:
        self.assert_run(CLEAN_BUILD, (0, OK))

    def test_build_with_a_linter_warning_fails_on_both_warning_lines(self) -> None:
        expected = (
            "LOG:2: warning: Peluang/Independence/Composition.lean:15:9: "
            "Variable name `x` is not explicitly referenced.\n"
            "LOG:4: Hint: The binding can be removed (if unused) or named `_` (if used implicitly). "
            "Alternatively, prefix the name with `_` to silence this warning:\n"
            "check_lake_log: 2 failure(s)\n"
        )
        self.assert_run(WARNING_BUILD, (1, expected))

    def test_build_without_the_audit_line_fails(self) -> None:
        expected = "LOG: 0 audit line(s), expected exactly 1\ncheck_lake_log: 1 failure(s)\n"
        self.assert_run(NO_AUDIT_BUILD, (1, expected))


if __name__ == "__main__":
    unittest.main()
