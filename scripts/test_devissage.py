"""Keep the devissage statement, native owners and public registrations aligned."""

import hashlib
import json
from pathlib import Path
import unittest

import catalog
import lint_style


ROOT = Path(__file__).resolve().parents[1]


class DevissageTests(unittest.TestCase):
    def test_public_scope_and_native_tests(self):
        entries = catalog.load_library()["entries"]
        self.assertEqual(entries["COL-0244"]["section"], "exact-categories")
        self.assertEqual(entries["COL-0245"]["section"], "restricted-spans")
        self.assertEqual(entries["COL-0246"]["section"], "quillen-k-theory")
        self.assertIn("no extension-closure assumption", entries["COL-0246"]["scope"])
        for name in ("ColibTest.Devissage", "ColibTest.ResolutionDevissage"):
            self.assertIn(name, lint_style.source_modules(ROOT, "ColibTest"))

    def test_actual_inclusion_and_shared_faithfulness(self):
        theorem = (ROOT / "Colib/KTheory/Quillen/Devissage/Theorem.lean").read_text()
        self.assertIn("(exactInclusion P).normalizedQ", theorem)
        self.assertIn("(exactInclusion P).KEquivOfHomotopyEquiv", theorem)
        self.assertIn("theorem KEquiv_coe", theorem)
        self.assertIn("KMap P n := rfl", theorem)
        lower = "Colib.CategoryTheory.ExactCategory.Functor.QFaithful"
        faithful = (ROOT / (lower.replace(".", "/") + ".lean")).read_text()
        old = (ROOT / "Colib/KTheory/Quillen/Equivalence.lean").read_text()
        self.assertIn("theorem mapQ_faithful_of_fullyFaithful", faithful)
        self.assertNotIn("theorem mapQ_faithful_of_fullyFaithful", old)
        self.assertIn("public import " + lower, old)
        inclusion = (ROOT / "Colib/CategoryTheory/Abelian/Devissage/QInclusion.lean").read_text()
        self.assertIn("(exactInclusion P).mapQ_faithful_of_fullyFaithful", inclusion)
        self.assertIn("abelianExactStructure P.FullSubcategory", inclusion)
        self.assertNotIn("ExactSubcategory.exactStructure", inclusion)

    def test_reviewed_production_crosswalk_matches_sources(self):
        crosswalk = json.loads((ROOT / "docs/migration/devissage/source-crosswalk.json").read_text())
        self.assertEqual(crosswalk["source_revision"],
                         "c561118b7795eb9780be9ed391c3251d6a4d0afd")
        self.assertEqual(len(crosswalk["declarations"]), 64)
        root_imports = (ROOT / "Colib.lean").read_text()
        for row in crosswalk["files"] + crosswalk["prerequisite_provenance"]:
            source = ROOT / row["target"]
            self.assertEqual(hashlib.sha256(source.read_bytes()).hexdigest(),
                             row["target_sha256"], row["target"])
            module = row["target"].removesuffix(".lean").replace("/", ".")
            self.assertIn("public import " + module, root_imports)
            self.assertNotIn("public import Aglib.", source.read_text())
            self.assertNotIn("public import Quillen.", source.read_text())


if __name__ == "__main__":
    unittest.main()
