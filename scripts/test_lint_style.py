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


if __name__ == "__main__":
    unittest.main()
