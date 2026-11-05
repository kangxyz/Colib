"""Regression tests for Library ownership, permanent IDs and compiled reference integrity."""

from pathlib import Path
import shutil
import json
import subprocess
import sys
import tempfile
import unittest

import catalog


class LibraryTests(unittest.TestCase):
    def setUp(self):
        self.library = catalog.load_library()
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        shutil.copytree(catalog.ROOT / "docs/library", self.root / "docs/library")
        shutil.copyfile(
            catalog.ROOT / "docs/references.toml", self.root / "docs/references.toml"
        )

    def native_fixture(self):
        native = {
            "bindings": [],
            "citations": [],
            "stacks": [],
            "declarations": [],
            "modules": [],
        }
        module_names = {
            "projective-dimension": "Colib.RingTheory.Koszul.Ext",
            "koszul-coefficients": "Colib.RingTheory.Koszul.Coefficients",
            "exact-categories": "Colib.CategoryTheory.ExactCategory.Basic",
            "bicategories": "Colib.CategoryTheory.Bicategory.IsoQuotient",
            "restricted-spans": "Colib.CategoryTheory.QConstruction.Basic",
            "grothendieck-groups": "Colib.KTheory.GrothendieckGroup.Field",
            "milnor-k-theory": "Colib.KTheory.MilnorK.DegreeTwo",
            "finite-algebra-coefficients": "Colib.RingTheory.Length.FiniteAlgebra",
        }
        native["modules"] = [
            {"name": name, "imports": []} for name in sorted(set(module_names.values()))
        ]
        for identifier in self.library["entries"]:
            name = "CategoryTheory.example_" + identifier.removeprefix("COL-")
            native["bindings"].append({"name": name, "id": identifier})
            native["declarations"].append(
                {
                    "name": name,
                    "type": "Prop",
                    "module": module_names[
                        self.library["entries"][identifier]["section"]
                    ],
                    "dependencies": [],
                }
            )
            native["citations"].append(
                {
                    "name": name,
                    "source": "stacks",
                    "locator": "fixture",
                    "relation": "comparison",
                    "scope": "Metadata-validation fixture",
                }
            )
        return native

    def test_initial_ids_keep_their_owners(self):
        self.assertTrue(
            {f"COL-{index:04d}" for index in range(1, 13)}
            <= self.library["entries"].keys()
        )
        self.assertEqual(
            self.library["entries"]["COL-0004"]["section"], "grothendieck-groups"
        )

    def test_exact_foundations_and_k0_ids_keep_their_owners(self):
        for index in range(15, 18):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"],
                "exact-categories",
            )
        for index in range(18, 21):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"],
                "grothendieck-groups",
            )
        native = self.native_fixture()
        result = catalog.compile_library(self.library, native, {}, "main")
        self.assertEqual(
            result["sections"]["exact-categories"]["modules"],
            ["Colib.CategoryTheory.ExactCategory.Basic"],
        )

    def test_exact_functor_and_subgroup_ids_keep_their_owners(self):
        self.assertEqual(
            self.library["entries"]["COL-0023"]["section"], "exact-categories"
        )
        for index in range(24, 27):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"],
                "grothendieck-groups",
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(23, 27):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_serre_localization_ids_keep_their_owners(self):
        self.assertEqual(
            self.library["entries"]["COL-0027"]["section"], "exact-categories"
        )
        for index in (28, 29):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"],
                "grothendieck-groups",
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(27, 30):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_admissible_pullback_ids_keep_their_owners(self):
        for index in (32, 33):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"],
                "exact-categories",
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in (32, 33):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_quotient_and_restricted_span_ids_keep_their_owners(self):
        self.assertEqual(self.library["entries"]["COL-0034"]["section"], "bicategories")
        self.assertEqual(self.library["entries"]["COL-0035"]["section"], "restricted-spans")
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for identifier in ("COL-0034", "COL-0035"):
            self.assertTrue(result["entries"][identifier]["references"])

    def test_unknown_reference_is_rejected(self):
        native = self.native_fixture()
        native["citations"][0]["source"] = "missing"
        with self.assertRaisesRegex(ValueError, "Unknown bibliographic key"):
            catalog.compile_library(self.library, native, {}, "main")

    def test_item_requires_a_compiled_binding(self):
        native = self.native_fixture()
        native["bindings"].pop()
        with self.assertRaisesRegex(ValueError, "needs a compiled"):
            catalog.compile_library(self.library, native, {}, "main")

    def test_multiple_literature_references_are_retained(self):
        native = self.native_fixture()
        extra = dict(
            native["citations"][0], source="WeibelKBook", locator="II, Definition 6.1.1"
        )
        native["citations"].append(extra)
        result = catalog.compile_library(self.library, native, {}, "main")
        identifier = native["bindings"][0]["id"]
        self.assertEqual(
            {ref["source"] for ref in result["entries"][identifier]["references"]},
            {"stacks", "WeibelKBook"},
        )

    def test_citation_does_not_require_a_permanent_item_tag(self):
        native = self.native_fixture()
        native["declarations"].append(
            {
                "name": "CategoryTheory.helper",
                "type": "Prop",
                "module": "Colib.KTheory.GrothendieckGroup.Field",
                "dependencies": [],
            }
        )
        native["citations"].append(
            {
                "name": "CategoryTheory.helper",
                "source": "WeibelKBook",
                "locator": "II, section 2",
                "relation": "ingredient",
                "scope": "Fixture",
            }
        )
        result = catalog.compile_library(self.library, native, {}, "main")
        self.assertTrue(
            any(ref["name"] == "CategoryTheory.helper" for ref in result["citations"])
        )
        self.assertFalse(
            any(
                "CategoryTheory.helper" in item["declarations"]
                for item in result["entries"].values()
            )
        )

    def test_duplicate_id_is_rejected(self):
        path = self.root / "docs/library/entries/k-theory/COL-0002.toml"
        path.write_text(path.read_text().replace('id = "COL-0002"', 'id = "COL-0001"'))
        with self.assertRaisesRegex(ValueError, "duplicate Library ID"):
            catalog.load_library(self.root)

    def test_hand_maintained_dependencies_are_rejected(self):
        path = self.root / "docs/library/entries/k-theory/COL-0001.toml"
        path.write_text(path.read_text() + 'requires = ["COL-0002"]\n')
        with self.assertRaisesRegex(ValueError, "dependencies come from Lean"):
            catalog.load_library(self.root)

    def test_hand_maintained_module_routes_are_rejected(self):
        path = self.root / "docs/library/chapters/k-theory.toml"
        path.write_text(path.read_text() + 'modules = ["Colib.KTheory"]\n')
        with self.assertRaisesRegex(ValueError, "Module ownership is exported"):
            catalog.load_library(self.root)

    def test_module_ownership_is_exported(self):
        native = self.native_fixture()
        result = catalog.compile_library(self.library, native, {}, "main")
        self.assertIn(
            "Colib.KTheory.GrothendieckGroup.Field",
            result["sections"]["grothendieck-groups"]["modules"],
        )

    def test_declaration_lists_are_owned_by_lean(self):
        path = self.root / "docs/library/entries/k-theory/COL-0001.toml"
        path.write_text(
            path.read_text() + 'declarations = ["CategoryTheory.GrothendieckGroup"]\n'
        )
        with self.assertRaisesRegex(ValueError, "belong in Lean attributes"):
            catalog.load_library(self.root)

    def test_editorial_move_retains_the_lean_defining_module(self):
        shutil.copytree(catalog.ROOT / "Colib", self.root / "Colib")
        for name in (
            "Colib.lean",
            "lakefile.toml",
            "lake-manifest.json",
            "lean-toolchain",
        ):
            shutil.copyfile(catalog.ROOT / name, self.root / name)
        built = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        built["source_hashes"] = catalog.source_hashes(self.root)
        directory = self.root / "build/library"
        directory.mkdir(parents=True)
        (directory / "library.json").write_text(json.dumps(built))
        entry = self.root / "docs/library/entries/k-theory/COL-0004.toml"
        entry.write_text(
            entry.read_text().replace(
                'section = "grothendieck-groups"', 'section = "milnor-k-theory"'
            )
        )
        scripts = self.root / "scripts"
        scripts.mkdir()
        shutil.copyfile(catalog.ROOT / "scripts/catalog.py", scripts / "catalog.py")
        result = subprocess.run(
            [sys.executable, str(scripts / "catalog.py"), "show", "COL-0004"],
            check=True,
            capture_output=True,
            text=True,
        )
        item = json.loads(result.stdout)
        self.assertEqual(item["section"], "milnor-k-theory")
        self.assertEqual(item["modules"], ["Colib.KTheory.GrothendieckGroup.Field"])

    def test_unsafe_bibliographic_path_is_rejected(self):
        path = self.root / "docs/references.toml"
        path.write_text(path.read_text() + '\n[sources."../../escape"]\n')
        with self.assertRaisesRegex(ValueError, "Unsafe bibliographic key"):
            catalog.load_library(self.root)

    def test_unknown_source_provider_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "Unsupported catalog source"):
            catalog.source_link("OtherLibrary.Result", {}, "main")


if __name__ == "__main__":
    unittest.main()
