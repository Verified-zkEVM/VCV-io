#!/usr/bin/env python3
"""Offline tests for review routing and trusted-profile composition."""

import importlib.util
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True

spec = importlib.util.spec_from_file_location("prepare_review", Path(__file__).with_name("prepare-review.py"))
review = importlib.util.module_from_spec(spec)
spec.loader.exec_module(review)


class PrepareReviewTests(unittest.TestCase):
    def test_general_review(self):
        for command, focus in [("/review", ""), ("/review Check Foo.lean\nSecond line", "Check Foo.lean\nSecond line")]:
            self.assertEqual(review.prepare_instructions(command, "POLICY"), ("general", focus))

    def test_tactic_review_uses_trusted_profile(self):
        self.assertEqual(review.prepare_instructions("/review tactics", "TRUSTED\n"), ("tactics", "TRUSTED"))
        self.assertEqual(
            review.prepare_instructions("/review\ttactics\nFocus on `fun_prop`\nThen casts", "TRUSTED\n"),
            ("tactics", "TRUSTED\n\nAdditional review focus:\nFocus on `fun_prop`\nThen casts"),
        )

    def test_exact_command_tokens(self):
        for command in ["/reviewer", "/reviews tactics", "text /review tactics"]:
            self.assertIsNone(review.prepare_instructions(command, "POLICY"))
        self.assertEqual(review.prepare_instructions("/review tactics_extra", "POLICY"), ("general", "tactics_extra"))

    def test_focus_is_literal_data(self):
        focus = '$(touch /tmp/should-not-exist) `false`\nrequested=false\n${{ secrets.TEST }}'
        self.assertEqual(review.prepare_instructions("/review " + focus, "POLICY"), ("general", focus))

    def test_output_preserves_multiline_value(self):
        value = "line one\nEOF\nrequested=false\nline four"
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "output"
            review.write_output(path, "instructions", value)
            first, remainder = path.read_text().split("\n", 1)
            name, delimiter = first.split("<<", 1)
            self.assertEqual(name, "instructions")
            self.assertNotIn(delimiter, value)
            self.assertEqual(remainder, value + "\n" + delimiter + "\n")

    def test_cli_uses_explicit_profile_outside_pr_checkout(self):
        script = Path(__file__).with_name("prepare-review.py").resolve()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            trusted = root / "trusted.md"
            trusted.write_text("TRUSTED PROFILE\n")
            checkout = root / "pr-checkout"
            checkout.mkdir()
            (checkout / "trusted.md").write_text("PR CONTENT\n")
            output = root / "output"
            subprocess.run(
                [sys.executable, str(script), "--profile", str(trusted)],
                cwd=checkout,
                env={**os.environ, "COMMENT_BODY": "/review tactics Focus on casts",
                     "GITHUB_OUTPUT": str(output)},
                check=True,
            )
            content = output.read_text()
            self.assertIn("\ntrue\n", content)
            self.assertIn("\ntactics\n", content)
            self.assertIn("TRUSTED PROFILE\n\nAdditional review focus:\nFocus on casts", content)
            self.assertNotIn("PR CONTENT", content)


if __name__ == "__main__":
    unittest.main()
