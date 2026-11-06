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

            def native(args, *, cwd, env, check):
                self.assertEqual(cwd, root)
                self.assertEqual(args[-2:], ["Colib.ColibStyleLintInputs",
                                               "ColibTest.ColibStyleLintInputs"])
                hubs = Path(env["LEAN_SRC_PATH"].split(":")[0])
                production = (hubs / "Colib/ColibStyleLintInputs.lean").read_text()
                tests = (hubs / "ColibTest/ColibStyleLintInputs.lean").read_text()
                self.assertEqual(production, "import Colib\nimport Colib.CategoryTheory.Own\n")
                self.assertEqual(tests, "import ColibTest.Leaf\n")
                return subprocess_result

            subprocess_result = type("Result", (), {"returncode": 17})()
            with patch.object(lint_style.subprocess, "run", side_effect=native):
                self.assertEqual(lint_style.main(root), 17)


if __name__ == "__main__":
    unittest.main()
