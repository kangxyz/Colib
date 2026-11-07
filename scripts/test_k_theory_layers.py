"""General categorical K-theory must not depend on its ring or scheme applications."""

from collections import deque
from pathlib import Path
import re
import unittest

import catalog


ROOT = Path(__file__).resolve().parents[1]
APPLICATION_PREFIXES = (
    "Colib.RingTheory.KTheory.",
    "Colib.AlgebraicGeometry.KTheory.",
)


def imports(source):
    # Drop nested Lean comments before inspecting the actual import commands.
    depth = 0
    kept = []
    for token in re.split(r"(/-|-/|--[^\n]*)", source):
        if token == "/-":
            depth += 1
        elif token == "-/":
            depth -= 1
        elif not depth and not token.startswith("--"):
            kept.append(token)
    return re.findall(r"^(?:public |private )?import (Colib\.[\w.]+)",
                      "".join(kept), re.MULTILINE)


class KTheoryLayersTests(unittest.TestCase):
    def test_general_theory_has_no_transitive_application_imports(self):
        graph = {
            ".".join(path.relative_to(ROOT).with_suffix("").parts): imports(path.read_text())
            for path in (ROOT / "Colib").rglob("*.lean")
        }
        roots = sorted(module for module in graph if module.startswith("Colib.KTheory."))
        self.assertTrue(roots)
        for root in roots:
            queue = deque([(root, [root])])
            seen = {root}
            while queue:
                module, path = queue.popleft()
                self.assertFalse(module.startswith(APPLICATION_PREFIXES), " -> ".join(path))
                for dependency in graph.get(module, []):
                    if dependency not in seen:
                        seen.add(dependency)
                        queue.append((dependency, path + [dependency]))

    def test_ring_and_scheme_source_families_have_application_owners(self):
        general = ROOT / "Colib/KTheory"
        for family in ("MilnorK", "Plus", "Quillen/Field", "GTheory/FiniteModules", "Scheme"):
            self.assertFalse(any((general / family).rglob("*.lean")), family)
        for module in ("GrothendieckGroup/Field", "GrothendieckGroup/FieldExact",
                       "Waldhausen/PerfectRestriction", "Quillen/LowDegreeScalarAction/FieldSymbols"):
            self.assertFalse((general / (module + ".lean")).exists(), module)
        self.assertFalse(list((general / "Quillen").glob("ProjectiveCompletion*.lean")))
        self.assertFalse(list((general / "Quillen").glob("Stable*Fiber*.lean")))

    def test_library_separates_general_and_applied_results(self):
        library = catalog.load_library()
        for section in ("grothendieck-groups", "quillen-k-theory", "waldhausen-k-theory"):
            self.assertEqual(library["sections"][section]["chapter"], "k-theory")
        for section in ("k-zero-of-fields", "milnor-k-theory",
                        "quillen-k-theory-of-rings", "g-theory-of-rings", "k-theory-of-schemes"):
            self.assertEqual(library["sections"][section]["chapter"],
                             "k-theory-rings-schemes")
        expected = {
            "COL-0004": "k-zero-of-fields",
            "COL-0020": "k-zero-of-fields",
            "COL-0230": "k-theory-of-schemes",
            "COL-0262": "quillen-k-theory-of-rings",
            "COL-0272": "quillen-k-theory",
            "COL-0273": "g-theory-of-rings",
            "COL-0274": "g-theory-of-rings",
            "COL-0279": "milnor-k-theory",
            "COL-0280": "quillen-k-theory-of-rings",
            "COL-0281": "quillen-k-theory",
        }
        for item, section in expected.items():
            self.assertEqual(library["entries"][item]["section"], section)

    def test_scalar_operation_and_module_specializations_are_separate(self):
        general = (ROOT / "Colib/KTheory/Quillen/LowDegreeScalarAction/ScalarUnit.lean").read_text()
        modules = (ROOT / "Colib/RingTheory/KTheory/Quillen/LowDegreeScalarAction/ScalarUnit.lean")
        application = modules.read_text()
        self.assertIn("namespace CategoryTheory.ExactCategory.ScalarUnit", general)
        self.assertIn("namespace CategoryTheory.ExactCategory.ScalarUnit", application)
        self.assertIn("def kOneAction :", general)
        self.assertIn("def smallModelKOneAction :", general)
        for name in ("finiteModule_scalarNatAut_apply", "finiteProjective_scalarNatAut_apply",
                     "finiteProjectiveKOneAction", "finiteModuleKOneAction",
                     "upperFiniteModuleKOneAction"):
            self.assertNotIn(name, general)
            self.assertIn(name, application)
        self.assertFalse(any("FGModuleCat" in module or "FiniteProjective" in module
                             for module in imports(general)))

    def test_import_parser_ignores_nested_comments(self):
        source = "/- import Colib.Fake /- nested -/ -/\npublic import Colib.Actual.Module\n"
        self.assertEqual(imports(source), ["Colib.Actual.Module"])


if __name__ == "__main__":
    unittest.main()
