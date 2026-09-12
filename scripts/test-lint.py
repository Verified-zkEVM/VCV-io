#!/usr/bin/env python3
"""Exercise upstream-linter orchestration, source coverage, and safe exception pruning."""

import importlib.util
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch


spec = importlib.util.spec_from_file_location("lint", Path(__file__).with_name("lint.py"))
lint = importlib.util.module_from_spec(spec)
spec.loader.exec_module(lint)


class LintTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix="vcvio-test-lint-")
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        previous = Path.cwd()
        os.chdir(self.root)
        self.addCleanup(os.chdir, previous)

    def tool(self, body):
        path = self.root / "linter"
        path.write_text("#!/usr/bin/env python3\n" + body)
        path.chmod(0o755)
        return str(path)

    def test_collection_unions_libraries_without_changing_committed_baseline(self):
        baseline = '[["docBlame", "A.f"], ["docBlame", "B.g"], ["docBlame", "A.old"]]'
        lint.BASELINE.parent.mkdir()
        lint.BASELINE.write_text(baseline)
        tool = self.tool('''import json, pathlib, sys
root = sys.argv[-1]
assert sys.argv[1:3] == ["--update", "--no-build"]
p = pathlib.Path("scripts/nolints.json")
assert len(json.loads(p.read_text())) == 3
p.write_text(json.dumps([["docBlame", root + (".f" if root == "A" else ".g")]]))
print("-- Linting passed for " + root + ".")
''')
        current = lint.collect(tool, ["A", "B"], baseline)
        self.assertEqual(current, {("docBlame", "A.f"), ("docBlame", "B.g")})
        self.assertEqual(lint.BASELINE.read_text(), baseline)
        lint.check_delta(current, lint.read_pairs(baseline, "test"), prune=True)
        lint.write_baseline(lint.BASELINE, current)
        self.assertEqual(lint.read_pairs(lint.BASELINE.read_text(), "test"), current)

    def test_failed_library_cannot_prune(self):
        tool = self.tool('import sys\nsys.exit(7)\n')
        with self.assertRaises(subprocess.CalledProcessError) as caught:
            lint.collect(tool, ["A"], "[]")
        self.assertEqual(caught.exception.returncode, 7)

    def test_incomplete_collection_is_rejected(self):
        tool = self.tool('print("interrupted before collection")\n')
        with self.assertRaisesRegex(ValueError, "Incomplete"):
            lint.collect(tool, ["A"], "[]")

    def test_stale_entries_fail_check_but_allow_prune(self):
        baseline = {("docBlame", "A.f")}
        with self.assertRaisesRegex(ValueError, "Obsolete"):
            lint.check_delta(set(), baseline, prune=False)
        lint.check_delta(set(), baseline, prune=True)

    def test_additions_fail_check_and_prune(self):
        for prune in (False, True):
            with self.assertRaisesRegex(ValueError, "Unlisted"):
                lint.check_delta({("docBlame", "A.new")}, set(), prune=prune)

    def test_duplicate_and_malformed_baselines_fail(self):
        for value in ('[["x", "y"], ["x", "y"]]', '{}', '[["x"]]', '[["x", 3]]'):
            with self.assertRaises(ValueError):
                lint.read_pairs(value, "test")

    def test_style_includes_unimported_test_file(self):
        files = []
        for root in ("A", *lint.TEST_ROOTS, "Interop"):
            path = Path(root) / "Leaf.lean"
            path.parent.mkdir()
            path.write_text("-- source\n")
            files.append(("100644", str(path)))
        Path("VCVioTest/Leaf.lean").write_text("-- deliberately bad style  \n")
        tool = self.tool('''import os, pathlib, sys
scratch = pathlib.Path(os.environ["LEAN_SRC_PATH"].split(os.pathsep)[0])
sources = []
for name in sys.argv[1:]:
    imports = (scratch / (name.replace(".", "/") + ".lean")).read_text().splitlines()
    sources.extend(line.removeprefix("import ") for line in imports)
assert len(sources) == len(set(sources)) == 5
assert "VCVioTest.Leaf" in sources
assert pathlib.Path("VCVioTest/Leaf.lean").read_text().endswith("  \\n")
sys.exit(23)
''')
        with patch.object(lint, "git_files", return_value=files), \
                patch.object(lint, "executable", return_value=tool):
            with self.assertRaises(subprocess.CalledProcessError) as caught:
                lint.style(["A"])
        self.assertEqual(caught.exception.returncode, 23)

    def test_hygiene_checks(self):
        for files in ([('100755', 'A/Bad.lean')],
                      [('100644', 'A/Foo.txt'), ('100644', 'A/foo.txt')]):
            with self.assertRaises(ValueError):
                lint.style_modules(files, ["A"])

    def test_source_discovery_includes_untracked_but_respects_gitignore(self):
        subprocess.run(["git", "init", "-q"], check=True)
        Path(".gitignore").write_text("ignored/\n")
        Path("A").mkdir()
        Path("A/Tracked.lean").write_text("-- tracked\n")
        subprocess.run(["git", "add", ".gitignore", "A/Tracked.lean"], check=True)
        Path("A/New.lean").write_text("-- new source\n")
        Path("ignored").mkdir()
        Path("ignored/Generated.lean").write_text("-- ignored\n")
        files = lint.git_files()
        self.assertIn(("100644", "A/New.lean"), files)
        self.assertNotIn("ignored/Generated.lean", [path for _, path in files])
        self.assertEqual(lint.style_modules(files, ["A"]),
                         {"A": ["A.New", "A.Tracked"]})

    def test_atomic_write_preserves_baseline_on_replace_failure(self):
        path = Path("nolints.json")
        path.write_text('[["docBlame", "A.f"]]\n')
        before = path.read_bytes()
        with patch.object(os, "replace", side_effect=OSError("cannot replace")):
            with self.assertRaises(OSError):
                lint.write_baseline(path, set())
        self.assertEqual(path.read_bytes(), before)
        self.assertEqual(list(Path('.').glob('.nolints-*')), [])

    def test_pruning_cannot_accept_baseline_additions_against_base_ref(self):
        subprocess.run(["git", "init", "-q"], check=True)
        lint.BASELINE.parent.mkdir()
        lint.BASELINE.write_text('[["docBlame", "A.f"]]\n')
        subprocess.run(["git", "add", str(lint.BASELINE)], check=True)
        subprocess.run(["git", "-c", "user.name=Lint test", "-c",
                        "user.email=lint-test@example.invalid", "-c", "commit.gpgSign=false",
                        "commit", "-qm", "Baseline"], check=True)
        lint.BASELINE.write_text('[["docBlame", "A.f"], ["docBlame", "A.new"]]\n')
        before = lint.BASELINE.read_bytes()
        with patch.object(lint, "collect") as collect:
            with self.assertRaisesRegex(ValueError, "additions relative to the merge base"):
                lint.environment(["A"], no_build=True, prune=True, base_ref="HEAD")
            collect.assert_not_called()
        self.assertEqual(lint.BASELINE.read_bytes(), before)


if __name__ == "__main__":
    unittest.main()
