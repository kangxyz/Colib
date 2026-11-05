"""Regression checks for the hand-maintained mathematical catalog boundary."""

import tempfile
from pathlib import Path
import unittest

import catalog


class CatalogTests(unittest.TestCase):
    def setUp(self):
        self.sources, self.entries = catalog.load_catalog()

    def test_initial_index_has_permanent_identifiers(self):
        self.assertTrue({f"COL-{index:04d}" for index in range(1, 13)} <=
                        {entry["id"] for entry in self.entries})
        self.assertEqual(len({entry["id"] for entry in self.entries}), len(self.entries))

    def test_unknown_reference_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "docs/catalog").mkdir(parents=True)
            source = catalog.ROOT / "docs/references.toml"
            (root / "docs/references.toml").write_bytes(source.read_bytes())
            original = catalog.ROOT / "docs/catalog/pilot.toml"
            text = original.read_text().replace('reference = "stacks"', 'reference = "missing"', 1)
            (root / "docs/catalog/pilot.toml").write_text(text)
            with self.assertRaisesRegex(ValueError, "unknown bibliographic key"):
                catalog.load_catalog(root)

    def test_duplicate_identifier_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "docs/catalog").mkdir(parents=True)
            (root / "docs/references.toml").write_bytes(
                (catalog.ROOT / "docs/references.toml").read_bytes()
            )
            original = (catalog.ROOT / "docs/catalog/pilot.toml").read_text()
            text = original.replace('id = "COL-0002"', 'id = "COL-0001"', 1)
            (root / "docs/catalog/pilot.toml").write_text(text)
            with self.assertRaisesRegex(ValueError, "duplicate catalog ID"):
                catalog.load_catalog(root)


if __name__ == "__main__":
    unittest.main()
