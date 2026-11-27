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

REPO = Path(__file__).resolve().parent.parent

OK = "check_lake_log: ok (1 audit line, 0 warning lines)\n"
NO_NAME = "check_lake_log: failed (package name not read)\n"
NO_LOG = "check_lake_log: failed (log not read)\n"

LAKEFILE = """\
import Lake
open Lake DSL

package «Demo» where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib «Demo»
"""

AUDIT = "info: DemoTest/Audit.lean:19:0: demoTest audit: 38 files, 37 imported DemoTest modules\n"

CLEAN_BUILD = """\
✔ [4342/4355] Built Demo.Independence.Composition (2.3s)
✔ [4347/4355] Built DemoTest.Independence.Composition (1.3s)
ℹ [4351/4355] Built DemoTest.Lint (2.4s)
info: DemoTest/Lint.lean:16:0: -- Found 0 errors in 336 declarations (plus 179 automatically generated ones) in Demo with 15 linters


-- All linting checks passed!
ℹ [4353/4355] Built DemoTest.Audit (1.4s)
info: DemoTest/Audit.lean:19:0: demoTest audit: 38 files, 37 imported DemoTest modules
Build completed successfully (4355 jobs).
"""

WARNING_BUILD = """\
⚠ [4342/4355] Built Demo.Independence.Composition (2.3s)
warning: Demo/Independence/Composition.lean:15:9: Variable name `x` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _x

Note: This linter can be disabled with `set_option linter.unusedVariables false`
ℹ [4351/4355] Built DemoTest.Lint (2.4s)
info: DemoTest/Lint.lean:16:0: -- Found 0 errors in 336 declarations (plus 179 automatically generated ones) in Demo with 15 linters


-- All linting checks passed!
ℹ [4353/4355] Built DemoTest.Audit (1.4s)
info: DemoTest/Audit.lean:19:0: demoTest audit: 38 files, 37 imported DemoTest modules
Build completed successfully (4355 jobs).
"""

NO_AUDIT_BUILD = """\
✔ [4342/4355] Built Demo.Independence.Composition (2.3s)
ℹ [4351/4355] Built DemoTest.Lint (2.4s)
info: DemoTest/Lint.lean:16:0: -- Found 0 errors in 336 declarations (plus 179 automatically generated ones) in Demo with 15 linters


-- All linting checks passed!
✔ [4353/4355] Built DemoTest.Audit (1.4s)
Build completed successfully (4355 jobs).
"""


def failed(warnings: int, audits: int) -> str:
    return f"check_lake_log: failed ({warnings} warning line(s), {audits} audit line(s))\n"


def no_audit(audits: int = 0) -> str:
    return f"LOG: {audits} audit line(s), expected exactly 1\n"


def run(
    content: str | bytes | None, lakefile: str | None = LAKEFILE, stdout: io.TextIOBase | None = None
) -> tuple[int, str]:
    """The exit code and stdout of `main` on a log file that holds `content`, in a repo root whose
    `lean/lakefile.lean` holds `lakefile`. With `content` `None` the log file does not exist, and with
    `lakefile` `None` the lakefile does not exist. The path of the lakefile is replaced by `LAKEFILE` in
    stdout, then the path of the log by `LOG`. With `stdout` given, `main` prints to it and the text is empty."""
    out = stdout if stdout is not None else io.StringIO()
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp) / "repo"
        (root / "lean").mkdir(parents=True)
        lake = root / "lean" / "lakefile.lean"
        if lakefile is not None:
            lake.write_text(lakefile, encoding="utf-8")
        log = Path(tmp) / "lake-build.log"
        if content is not None:
            log.write_bytes(content.encode("utf-8") if isinstance(content, str) else content)
        with contextlib.redirect_stdout(out):
            code = cll.main(["check_lake_log.py", str(log), str(root)])
        text = "" if stdout is not None else out.getvalue().replace(str(lake), "LAKEFILE").replace(str(log), "LOG")
    return code, text


class Main(unittest.TestCase):
    def assert_run(self, content: str | bytes, expected: tuple[int, str]) -> None:
        got = run(content)
        self.assertEqual(got, expected, f"expected {expected!r}, observed {got!r}")

    def test_clean_log_passes_with_the_ok_line(self) -> None:
        self.assert_run("Built Demo\n" + AUDIT + "Build completed successfully (4355 jobs).\n", (0, OK))

    def test_one_warning_line_fails_and_names_its_line_number(self) -> None:
        expected = "LOG:2: warning: unused variable\n" + failed(1, 1)
        self.assert_run("Built Demo\nwarning: unused variable\n" + AUDIT, (1, expected))

    def test_warning_line_and_missing_audit_line_give_both_failures(self) -> None:
        expected = "LOG:1: warning: unused variable\n" + no_audit() + failed(1, 0)
        self.assert_run("warning: unused variable\nBuild completed successfully (4355 jobs).\n", (1, expected))

    def test_zero_audit_lines_fail(self) -> None:
        self.assert_run("Built Demo\nBuild completed successfully (4355 jobs).\n", (1, no_audit() + failed(0, 0)))

    def test_two_audit_lines_fail(self) -> None:
        self.assert_run(AUDIT + "Built Demo\n" + AUDIT, (1, no_audit(2) + failed(0, 2)))

    def test_warning_inside_a_longer_line_fails(self) -> None:
        line = "warning: Demo.lean:15:9: Variable name `x` is not explicitly referenced."
        for content, lineno in ((AUDIT + line + "\n", 2), (AUDIT + "\n\n  lake: " + line + " (1)\n", 4)):
            with self.subTest(content=content):
                shown = content.split("\n")[lineno - 1]
                self.assert_run(content, (1, f"LOG:{lineno}: {shown}\n" + failed(1, 1)))

    def test_audit_like_lines_that_do_not_match_are_not_counted(self) -> None:
        prefix = "info: DemoTest/Audit.lean:19:0: "
        for line in (
            prefix + "demoTest audit: x files, 37 imported DemoTest modules",
            prefix + "demoTest audit:  38 files, 37 imported DemoTest modules",
            prefix + "demoTest audit: files, 37 imported DemoTest modules",
            prefix + "demoTest audit: 38 file, 37 imported DemoTest modules",
            prefix + "demotest audit: 38 files, 37 imported DemoTest modules",
            prefix + "DemoTest audit: 38 files, 37 imported DemoTest modules",
            prefix + "demoTest audit: 38 files",
            "error: DemoTest/Audit.lean:19:0: demoTest audit: A does not import B",
            "error: DemoTest/Audit.lean:19:0: demoTest audit: 38 files, 37 imported DemoTest modules",
            "info: DemoTest/Lint.lean:19:0: demoTest audit: 38 files, 37 imported DemoTest modules",
            "info: OtherTest/Audit.lean:19:0: otherTest audit: 38 files, 37 imported OtherTest modules",
            "info: OtherTest/Audit.lean:19:0: demoTest audit: 38 files, 37 imported DemoTest modules",
            "info: DemoTest/Audit.lean:19:0: otherTest audit: 38 files, 37 imported DemoTest modules",
            "demoTest audit: 38 files, 37 imported DemoTest modules",
            "  " + AUDIT.rstrip("\n"),
            "- " + AUDIT.rstrip("\n"),
        ):
            with self.subTest(line=line):
                self.assert_run(line + "\n", (1, no_audit() + failed(0, 0)))
                self.assert_run(line + "\n" + AUDIT, (0, OK))

    def test_empty_log_fails_with_zero_audit_lines(self) -> None:
        self.assert_run("", (1, no_audit() + failed(0, 0)))

    def test_undecodable_bytes_are_replaced(self) -> None:
        self.assert_run(b"\xff\xfe Built\n" + AUDIT.encode("utf-8"), (0, OK))
        expected = "LOG:1: � warning: x\n" + failed(1, 1)
        self.assert_run(b"\xff warning: x\n" + AUDIT.encode("utf-8"), (1, expected))

    def test_crlf_log_passes_and_reports_a_warning_line_without_the_carriage_return(self) -> None:
        crlf_audit = AUDIT.replace("\n", "\r\n")
        self.assert_run("Built Demo\r\n" + crlf_audit, (0, OK))
        self.assert_run("warning: x\r\n" + crlf_audit, (1, "LOG:1: warning: x\n" + failed(1, 1)))

    def test_missing_log_fails(self) -> None:
        got = run(None)
        expected = (1, "LOG: missing\n" + NO_LOG)
        self.assertEqual(got, expected, f"expected {expected!r}, observed {got!r}")

    def test_directory_as_the_log_is_not_readable(self) -> None:
        out = io.StringIO()
        with tempfile.TemporaryDirectory() as tmp:
            (Path(tmp) / "lean").mkdir()
            (Path(tmp) / "lean" / "lakefile.lean").write_text(LAKEFILE, encoding="utf-8")
            with contextlib.redirect_stdout(out):
                code = cll.main(["check_lake_log.py", tmp, tmp])
        lines = out.getvalue().replace(tmp, "LOG").splitlines()
        got = (code, len(lines), lines[0][: len("LOG: not readable: ")], lines[-1] + "\n")
        expected = (1, 2, "LOG: not readable: ", NO_LOG)
        self.assertEqual(got, expected, f"expected {expected!r}, observed {got!r}")

    def test_character_that_stdout_cannot_encode_is_printed_as_an_escape(self) -> None:
        raw = io.BytesIO()
        out = io.TextIOWrapper(raw, encoding="ascii", errors="strict")
        code, _ = run("warning: unused ∀ binder\n" + AUDIT, stdout=out)
        out.flush()
        lines = raw.getvalue().decode("ascii").splitlines()
        got = (code, len(lines), lines[0].split(":1: ", 1)[-1], lines[-1] + "\n")
        expected = (1, 2, "warning: unused \\u2200 binder", failed(1, 1))
        self.assertEqual(got, expected, f"expected {expected!r}, observed {got!r}")

    def test_wrong_argument_count_exits_2_with_the_usage_line(self) -> None:
        for argv in (["check_lake_log.py"], ["check_lake_log.py", "a.log", "root", "more"]):
            with self.subTest(argv=argv):
                out, err = io.StringIO(), io.StringIO()
                with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
                    code = cll.main(argv)
                got = (code, out.getvalue(), err.getvalue())
                expected = (2, "", "Usage: check_lake_log.py LOG [REPO_ROOT]\n")
                self.assertEqual(got, expected, f"expected {expected!r}, observed {got!r}")


class PackageName(unittest.TestCase):
    def assert_run(self, content: str, lakefile: str | None, expected: tuple[int, str]) -> None:
        got = run(content, lakefile)
        self.assertEqual(got, expected, f"expected {expected!r}, observed {got!r}")

    def test_bare_package_name_is_read(self) -> None:
        self.assert_run(AUDIT, "import Lake\npackage Demo where\n", (0, OK))
        self.assert_run(AUDIT, "package Demo\n", (0, OK))

    def test_only_the_first_letter_goes_to_lower_case(self) -> None:
        audit = "info: DemoLibTest/Audit.lean:19:0: demoLibTest audit: 6 files, 5 imported DemoLibTest modules\n"
        lakefile = "package «DemoLib» where\n"
        self.assert_run(audit, lakefile, (0, OK))
        wrong = "info: DemoLibTest/Audit.lean:19:0: demolibTest audit: 6 files, 5 imported DemoLibTest modules\n"
        self.assert_run(wrong, lakefile, (1, no_audit() + failed(0, 0)))
        self.assert_run(AUDIT, lakefile, (1, no_audit() + failed(0, 0)))

    def test_package_name_with_a_regex_character_is_refused(self) -> None:
        expected = "LAKEFILE:1: package name `De.o` is not a letter followed by letters, digits or `_`\n" + NO_NAME
        self.assert_run(AUDIT, "package «De.o» where\n", (1, expected))

    def test_package_name_that_is_not_an_identifier_is_refused(self) -> None:
        for name, line in (('"demo"', 'package "demo" where'), ("", "package «» where"), ("9x", "package 9x")):
            with self.subTest(line=line):
                expected = f"LAKEFILE:3: package name `{name}` is not a letter followed by letters, digits or `_`\n"
                self.assert_run(AUDIT, "import Lake\n\n" + line + "\n", (1, expected + NO_NAME))

    def test_lakefile_without_a_package_line_fails(self) -> None:
        expected = "LAKEFILE: 0 package line(s), expected exactly 1\n" + NO_NAME
        for lakefile in ("", "import Lake\n", "-- package «Demo»\n", "  package «Demo»\n", "packages «Demo»\n"):
            with self.subTest(lakefile=lakefile):
                self.assert_run(AUDIT, lakefile, (1, expected))

    def test_lakefile_with_two_package_lines_fails(self) -> None:
        expected = "LAKEFILE: 2 package line(s), expected exactly 1\n" + NO_NAME
        self.assert_run(AUDIT, "package «Demo» where\npackage «Other» where\n", (1, expected))

    def test_missing_lakefile_fails_before_the_log_is_read(self) -> None:
        self.assert_run(AUDIT, None, (1, "LAKEFILE: missing\n" + NO_NAME))
        got = run(None, None)
        expected = (1, "LAKEFILE: missing\n" + NO_NAME)
        self.assertEqual(got, expected, f"expected {expected!r}, observed {got!r}")


class ThisRepo(unittest.TestCase):
    def test_the_audit_line_of_this_repo_passes_with_the_default_root(self) -> None:
        name, failure = cll.package_name(str(REPO / "lean" / "lakefile.lean"))
        self.assertIsNotNone(name, f"expected a package name, observed the failure {failure!r}")
        lower = name[0].lower() + name[1:]
        audit = f"info: {name}Test/Audit.lean:19:0: {lower}Test audit: 38 files, 37 imported {name}Test modules\n"
        out = io.StringIO()
        with tempfile.TemporaryDirectory() as tmp:
            log = Path(tmp) / "lake-build.log"
            log.write_text(audit, encoding="utf-8")
            with contextlib.redirect_stdout(out):
                code = cll.main(["check_lake_log.py", str(log)])
        got = (code, out.getvalue())
        self.assertEqual(got, (0, OK), f"expected {(0, OK)!r}, observed {got!r}")

    def test_the_library_of_this_repo_writes_the_audit_line_that_the_pattern_reads(self) -> None:
        name, failure = cll.package_name(str(REPO / "lean" / "lakefile.lean"))
        self.assertIsNotNone(name, f"expected a package name, observed the failure {failure!r}")
        lower = name[0].lower() + name[1:]
        audit_file = REPO / "lean" / f"{name}Test" / "Audit.lean"
        self.assertTrue(audit_file.is_file(), f"expected the file {audit_file}, observed no such file")
        linter = (REPO / "lean" / f"{name}Lint.lean").read_text(encoding="utf-8")
        message = f'm!"{lower}Test audit: {{files.size}} files, {{audited}} imported '
        self.assertIn(message, linter, f"expected {message!r} in {name}Lint.lean, observed no such text")


class BuildLogs(unittest.TestCase):
    def assert_run(self, content: str, expected: tuple[int, str]) -> None:
        got = run(content)
        self.assertEqual(got, expected, f"expected {expected!r}, observed {got!r}")

    def test_clean_build_passes(self) -> None:
        self.assert_run(CLEAN_BUILD, (0, OK))

    def test_build_with_one_linter_warning_reports_two_warning_lines(self) -> None:
        expected = (
            "LOG:2: warning: Demo/Independence/Composition.lean:15:9: "
            "Variable name `x` is not explicitly referenced.\n"
            "LOG:4: Hint: The binding can be removed (if unused) or named `_` (if used implicitly). "
            "Alternatively, prefix the name with `_` to silence this warning:\n" + failed(2, 1)
        )
        self.assert_run(WARNING_BUILD, (1, expected))

    def test_build_without_the_audit_line_fails(self) -> None:
        self.assert_run(NO_AUDIT_BUILD, (1, no_audit() + failed(0, 0)))


if __name__ == "__main__":
    unittest.main()
