"""The compact CI must not repackage Mathlib or mix Stacks into the Colib cache."""
import importlib.util
from pathlib import Path, PurePosixPath
import unittest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location('ci_cache', ROOT / '.github/ci/cache.py')
ci_cache = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(ci_cache)


class CacheBoundaryTests(unittest.TestCase):
    def test_only_root_and_development_tools_are_cached(self):
        paths = [PurePosixPath(value) for value in ci_cache.own_paths()]
        self.assertIn(PurePosixPath('.lake/build'), paths)
        self.assertIn(PurePosixPath('.lake/tools'), paths)
        self.assertNotIn(PurePosixPath('.lake'), paths)
        for forbidden in ['.lake/packages/mathlib/.lake/build/lib/lean/Mathlib',
                          '.lake/packages/Stacks/.lake/build', '.lake/native-cache']:
            target = PurePosixPath(forbidden)
            self.assertFalse(any(path == target or path in target.parents for path in paths))
        for package in ['mathlib', 'batteries']:
            self.assertIn(PurePosixPath(f'.lake/packages/{package}/.lake/build/bin'), paths)


if __name__ == '__main__':
    unittest.main()
