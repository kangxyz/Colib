"""Keep complete Serre localization, its actual maps and Library entry points aligned."""

import hashlib
import json
from pathlib import Path
import unittest

import catalog
import lint_style


ROOT = Path(__file__).resolve().parents[1]


class SerreLocalizationTests(unittest.TestCase):
    def test_complete_public_items_and_exact_scope(self):
        entries = catalog.load_library()["entries"]
        expected = {
            "COL-0247": "homotopy-colimits",
            "COL-0248": "classifying-spaces",
            "COL-0249": "quillen-k-theory",
            "COL-0250": "quillen-k-theory",
        }
        for item, section in expected.items():
            self.assertEqual(entries[item]["section"], section)
            self.assertEqual(entries[item]["kind"], "theorem")
            self.assertEqual(entries[item]["review"], "author_checked")
        self.assertIn("No monomorphism, injectivity, countability", entries["COL-0247"]["scope"])
        self.assertIn("transition homotopy equivalences", entries["COL-0248"]["scope"])
        self.assertIn("No global continuous homotopy inverse", entries["COL-0249"]["scope"])
        self.assertIn("original Quillen K-groups", entries["COL-0250"]["scope"])

    def test_reviewed_source_prefixes_and_generated_root(self):
        crosswalk = json.loads(
            (ROOT / "docs/migration/serre/integration-source-crosswalk.json").read_text())
        self.assertEqual(crosswalk["source_revision"],
                         "c561118b7795eb9780be9ed391c3251d6a4d0afd")
        self.assertEqual(crosswalk["items"],
                         ["COL-0247", "COL-0248", "COL-0249", "COL-0250"])
        self.assertEqual(len(crosswalk["files"]), 8)
        root_imports = (ROOT / "Colib.lean").read_text()
        for row in crosswalk["files"]:
            source = (ROOT / row["target"]).read_bytes()
            self.assertEqual(hashlib.sha256(source).hexdigest(), row["target_sha256"])
            prefix = source[:row["reviewed_prefix_bytes"]]
            self.assertEqual(hashlib.sha256(prefix).hexdigest(), row["reviewed_prefix_sha256"])
            module = row["target"].removesuffix(".lean").replace("/", ".")
            self.assertIn("public import " + module, root_imports)
            self.assertIn(f'colib_tag "{row["item"]}"', source.decode())
            self.assertNotIn("public import Quillen.", source.decode())
            self.assertNotIn("public import Aglib.", source.decode())

    def test_actual_comparison_boundary_and_independent_zero_tail(self):
        base = ROOT / "Colib/KTheory/Quillen/Localization/Serre"
        fiber = (base / "FiberEquivalence.lean").read_text()
        theorem = (base / "LocalizationTheorem.lean").read_text()
        self.assertIn("MulEquiv.ofBijective (localizationFiberComparisonHom P n)", fiber)
        self.assertIn("localizationFiberComparisonHom P n := rfl", fiber)
        self.assertIn("(localizationFiberEquiv P n).symm.toMonoidHom.comp", theorem)
        self.assertIn("surjective_KZero := quotientKZero_surjective P", theorem)
        self.assertIn("theorem connecting_unique", theorem)
        self.assertIn("theorem localization_KZero_tail", theorem)
        zero = (base / "KZero.lean").read_text()
        self.assertNotIn("public import Colib.KTheory.Quillen.Localization.Serre.FiberEquivalence",
                         zero)

    def test_regressions_remain_automatically_discovered(self):
        modules = lint_style.source_modules(ROOT, "ColibTest")
        for module in ("ColibTest.SerreFiberEquivalence",
                       "ColibTest.SerreLocalizationTheorem", "ColibTest.QuillenTheoremBFull"):
            self.assertIn(module, modules)
        check = (ROOT / "scripts/check.sh").read_text()
        for command in ("lake --log-level=error build Colib", "lake --log-level=error test",
                        "bash .github/lint/run.sh Colib", "python3 scripts/lint_style.py",
                        "lake exe mathlib/mk_all --lib Colib --check",
                        '"$auditor/.lake/build/bin/axiom-audit" --root Colib',
                        "python3 scripts/catalog.py build", "python3 scripts/site.py"):
            self.assertIn(command, check)


if __name__ == "__main__":
    unittest.main()
