#!/usr/bin/env python3
"""Check umbrella validation and restoration without invoking Lake."""

from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


UMBRELLAS = (
    "ToMathlib.lean", "VCVio.lean", "LatticeCrypto.lean", "Extern.lean",
    "HashSig.lean", "Examples.lean", "VCVioWidgets.lean", "VCVioTest.lean", "Interop.lean",
)


class CheckImportsTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="vcvio-import-check-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        scripts = self.root / "scripts"
        scripts.mkdir()
        shutil.copyfile(Path(__file__).with_name("check-imports.sh"), scripts / "check-imports.sh")
        for name in UMBRELLAS:
            (self.root / name).write_text(f"original {name}\n")

    def run_check(self, generator="exit 0\n"):
        update = self.root / "scripts/update-lib.sh"
        update.write_text("#!/usr/bin/env bash\nset -eu\n" + generator)
        update.chmod(0o755)
        return subprocess.run(
            ["/bin/bash", "scripts/check-imports.sh"], cwd=self.root,
            text=True, capture_output=True, timeout=10,
        )

    def assert_originals(self):
        for name in UMBRELLAS:
            self.assertEqual((self.root / name).read_text(), f"original {name}\n")

    def test_current_umbrellas_pass_unchanged(self):
        result = self.run_check()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assert_originals()

    def test_stale_umbrella_fails_and_restores(self):
        result = self.run_check("printf 'generated\\n' > ToMathlib.lean\n")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("ToMathlib.lean is out of date", result.stderr)
        self.assert_originals()

    def test_missing_umbrella_fails_before_generator(self):
        (self.root / "ToMathlib.lean").unlink()
        result = self.run_check("touch generator-ran\nprintf 'generated\\n' > ToMathlib.lean\n")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("required umbrella ToMathlib.lean is missing", result.stderr)
        self.assertFalse((self.root / "generator-ran").exists())
        self.assertFalse((self.root / "ToMathlib.lean").exists())

    def test_generator_failure_restores_partial_changes(self):
        result = self.run_check("printf 'partial\\n' > VCVio.lean\nexit 7\n")
        self.assertEqual(result.returncode, 7)
        self.assert_originals()

    def test_local_edits_are_restored_not_replaced_with_git(self):
        dirty = "user's uncommitted umbrella\n"
        (self.root / "VCVio.lean").write_text(dirty)
        result = self.run_check("printf 'generated\\n' > VCVio.lean\n")
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual((self.root / "VCVio.lean").read_text(), dirty)


if __name__ == "__main__":
    unittest.main()
