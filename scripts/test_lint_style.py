"""Check the source boundary passed to the native Mathlib text linter."""

from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import lint_style


class LintScopeTests(unittest.TestCase):
    def test_all_owned_sources_and_no_dependencies(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            files = ["Colib.lean", "Colib/CategoryTheory/Own.lean", "ColibTest/Leaf.lean",
                     ".lake/packages/Stacks/StacksFrontier/Other.lean"]
            for name in files:
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.touch()

            def native(args, *, cwd, check):
                self.assertEqual(cwd, root)
                for package, argument in zip(lint_style.PACKAGES, args[-2:]):
                    self.assertTrue(argument.startswith(package + ".ColibStyleLintInputs"))
                    self.assertTrue(argument.endswith(".Imports"))
                production = next((root / "Colib").glob("ColibStyleLintInputs*/Imports.lean")).read_text()
                tests = next((root / "ColibTest").glob("ColibStyleLintInputs*/Imports.lean")).read_text()
                self.assertEqual(production, "import Colib\nimport Colib.CategoryTheory.Own\n")
                self.assertEqual(tests, "import ColibTest.Leaf\n")
                return subprocess_result

            subprocess_result = type("Result", (), {"returncode": 17})()
            with patch.object(lint_style.subprocess, "run", side_effect=native):
                self.assertEqual(lint_style.main(root), 17)
            self.assertFalse(list(root.glob("*/ColibStyleLintInputs*")))


    def test_cleanup_after_native_exception(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for package in lint_style.PACKAGES:
                (root / package).mkdir()
                (root / package / "Leaf.lean").touch()
            with patch.object(lint_style.subprocess, "run", side_effect=OSError("native failure")):
                with self.assertRaisesRegex(OSError, "native failure"):
                    lint_style.main(root)
            self.assertFalse(list(root.glob("*/ColibStyleLintInputs*")))

    def test_existing_source_is_preserved(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for package in lint_style.PACKAGES:
                (root / package).mkdir()
                (root / package / "Leaf.lean").touch()
            existing = root / "ColibTest/ColibStyleLintInputs.lean"
            existing.write_text("-- Keep existing work.\n")
            result = type("Result", (), {"returncode": 0})()
            with patch.object(lint_style.subprocess, "run", return_value=result):
                self.assertEqual(lint_style.main(root), 0)
            self.assertEqual(existing.read_text(), "-- Keep existing work.\n")
            self.assertEqual(list(root.glob("*/ColibStyleLintInputs*")), [existing])



if __name__ == "__main__":
    unittest.main()
