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

    def test_completion_milestone_native_scope_and_ci(self):
        root = catalog.ROOT
        ledger = json.loads((root / "docs/migration/milnor-completion.json").read_text())
        self.assertEqual(ledger["library_item"], "COL-0168")
        self.assertEqual(ledger["source_file"],
                         "Aglib/KTheory/MilnorK/Residue/AdicCompletion.lean")
        source = (root / "Colib/KTheory/MilnorK/Residue/Completion.lean").read_text()
        for declaration in ledger["source_declarations"].values():
            self.assertIn(declaration.removeprefix("Stacks.Chow."), source)
        self.assertIn("IsFractionRing.lift", source)
        self.assertIn("AdicCompletion.residueField_map_bijective", source)
        self.assertIn("dvrMilnorTameSymbol'_completion_eq_zero_iff", source)
        self.assertIn('colib_tag "COL-0168"', source)
        for path in ("scripts/check.sh", ".github/workflows/lean-ci.yml"):
            self.assertIn("ColibTest.MilnorCompletion", (root / path).read_text())
        self.assertIn("Colib.KTheory.MilnorK.Residue.Completion",
                      (root / "Colib.lean").read_text())

    def test_principal_euler_complete_chain_registration(self):
        root = catalog.ROOT
        leaves = ("Basic", "Additivity", "Support", "Filtration", "Associativity")
        for number, leaf in zip(range(169, 174), leaves):
            identifier = f"COL-{number:04d}"
            self.assertEqual(self.library["entries"][identifier]["section"], "principal-euler")
            module = f"Colib.RingTheory.Multiplicity.PrincipalEuler.{leaf}"
            source = (root / (module.replace(".", "/") + ".lean")).read_text()
            self.assertIn(f'colib_tag "{identifier}"', source)
            self.assertIn(module, (root / "Colib.lean").read_text())
        for path in ("scripts/check.sh", ".github/workflows/lean-ci.yml"):
            self.assertIn("ColibTest.PrincipalEuler", (root / path).read_text())
        source = (root / "Colib/RingTheory/Multiplicity/PrincipalEuler/Associativity.lean").read_text()
        self.assertIn("principalEuler_quotient_closedPoint_eq_zero", source)
        self.assertIn("principalCokernel_associativity", source)

    def test_finite_algebra_local_length_registration(self):
        root = catalog.ROOT
        for identifier, leaf in (("COL-0180", "FiniteAlgebraFiber"),
                                 ("COL-0181", "FiniteAlgebraLocal")):
            self.assertEqual(self.library["entries"][identifier]["section"],
                             "finite-algebra-coefficients")
            module = f"Colib.RingTheory.Length.{leaf}"
            source = (root / (module.replace(".", "/") + ".lean")).read_text()
            self.assertIn(f'colib_tag "{identifier}"', source)
            self.assertIn(module, (root / "Colib.lean").read_text())
        for path in ("scripts/check.sh", ".github/workflows/lean-ci.yml"):
            self.assertIn("ColibTest.FiniteAlgebraLocal", (root / path).read_text())
        self.assertIn("specialization", self.library["entries"]["COL-0181"]["scope"])

    def test_finite_algebra_norm_chain_registration(self):
        root = catalog.ROOT
        modules = {"COL-0182": "Colib.LinearAlgebra.Determinant.FiniteLength",
                   "COL-0183": "Colib.RingTheory.Norm.FiniteAlgebra",
                   "COL-0184": "Colib.RingTheory.Norm.PolynomialFiber"}
        for identifier, module in modules.items():
            self.assertEqual(self.library["entries"][identifier]["section"],
                             "finite-algebra-coefficients")
            source = (root / (module.replace(".", "/") + ".lean")).read_text()
            self.assertIn(f'colib_tag "{identifier}"', source)
            self.assertIn(module, (root / "Colib.lean").read_text())
        for path in ("scripts/check.sh", ".github/workflows/lean-ci.yml"):
            self.assertIn("ColibTest.FiniteAlgebraNorm", (root / path).read_text())

    def test_completion_branches_chain_registration(self):
        root = catalog.ROOT
        leaves = ("FiniteAlgebra", "ChineseRemainder", "SemilocalBranches",
                  "DedekindBranches", "FiniteDedekindBranches")
        for number, leaf in zip(range(185, 190), leaves):
            identifier = f"COL-{number:04d}"
            self.assertEqual(self.library["entries"][identifier]["section"], "adic-completion")
            module = f"Colib.RingTheory.AdicCompletion.{leaf}"
            source = (root / (module.replace(".", "/") + ".lean")).read_text()
            self.assertIn(f'colib_tag "{identifier}"', source)
            self.assertIn(module, (root / "Colib.lean").read_text())
        for path in ("scripts/check.sh", ".github/workflows/lean-ci.yml"):
            self.assertIn("ColibTest.CompletionBranches", (root / path).read_text())

    def test_fraction_residue_chain_registration(self):
        root = catalog.ROOT
        modules = {
            "COL-0190": "Colib.RingTheory.Localization.FiniteProductBaseChange",
            "COL-0191": "Colib.RingTheory.AdicCompletion.BranchFraction",
            "COL-0192": "Colib.RingTheory.AdicCompletion.FractionBranches",
            "COL-0193": "Colib.RingTheory.Norm.DVRResidue",
            "COL-0194": "Colib.RingTheory.Norm.DVRResidue",
        }
        for identifier, module in modules.items():
            section = ("adic-completion" if identifier < "COL-0193"
                       else "finite-algebra-coefficients")
            self.assertEqual(self.library["entries"][identifier]["section"], section)
            source = (root / (module.replace(".", "/") + ".lean")).read_text()
            self.assertIn(f'colib_tag "{identifier}"', source)
            self.assertIn(module, (root / "Colib.lean").read_text())
        for path in ("scripts/check.sh", ".github/workflows/lean-ci.yml"):
            for module in ("ColibTest.FractionBranches", "ColibTest.DVRResidueNorm"):
                self.assertIn(module, (root / path).read_text())

    def test_uniformizer_norm_complete_chain_registration(self):
        root = catalog.ROOT
        modules = {
            "COL-0195": "Colib.RingTheory.Henselian.UniformizerNormalization",
            "COL-0196": "Colib.RingTheory.DiscreteValuationRing.RamificationDegree",
            "COL-0197": "Colib.RingTheory.Norm.UniformizerBinomial",
            "COL-0198": "Colib.RingTheory.Norm.DVRUniformizer",
            "COL-0199": "Colib.RingTheory.Norm.DVRPrimeUniformizer",
        }
        for identifier, module in modules.items():
            section = ("henselian-ramification" if identifier < "COL-0197"
                       else "finite-algebra-coefficients")
            self.assertEqual(self.library["entries"][identifier]["section"], section)
            source = (root / (module.replace(".", "/") + ".lean")).read_text()
            self.assertIn(f'colib_tag "{identifier}"', source)
            self.assertIn(module, (root / "Colib.lean").read_text())
        for path in ("scripts/check.sh", ".github/workflows/lean-ci.yml"):
            for test in ("HenselianPrincipalRoots", "HenselianUniformizerNormalization",
                         "DVRRamificationDegree", "DVRUniformizerBinomial",
                         "DVRUniformizerNorm", "DVRPrimeUniformizerNorm"):
                self.assertIn("ColibTest." + test, (root / path).read_text())
        self.assertIn("ordinary norm-order", self.library["entries"]["COL-0199"]["scope"])

    def test_native_dvr_norm_order_registration(self):
        root = catalog.ROOT
        modules = {
            "COL-0200": "Colib.RingTheory.DiscreteValuationRing.FractionOrder",
            "COL-0201": "Colib.RingTheory.Norm.DVROrder",
        }
        for identifier, module in modules.items():
            source = (root / (module.replace(".", "/") + ".lean")).read_text()
            self.assertIn(f'colib_tag "{identifier}"', source)
            self.assertIn(module, (root / "Colib.lean").read_text())
        for path in ("scripts/check.sh", ".github/workflows/lean-ci.yml"):
            for test in ("DVRFractionOrder", "DVRNormOrder"):
                self.assertIn("ColibTest." + test, (root / path).read_text())
        source = (root / "Colib/RingTheory/Norm/DVROrder.lean").read_text()
        self.assertIn("theorem neg_log_valuation_norm", source)
        self.assertIn("theorem dvrFracOrd_norm_mk0", source)
        self.assertNotIn("[PerfectField", source)
        self.assertNotIn("[HenselianLocalRing", source)

    def test_charpoly_branch_complete_chain_registration(self):
        root = catalog.ROOT
        modules = {
            "COL-0202": "Colib.RingTheory.Charpoly.Basic",
            "COL-0203": "Colib.RingTheory.Charpoly.TensorProduct",
            "COL-0204": "Colib.RingTheory.Charpoly.DVRResidue",
            "COL-0205": "Colib.RingTheory.Charpoly.IntegralTensorProduct",
            "COL-0206": "Colib.RingTheory.Polynomial.PowerFactorCount",
            "COL-0207": "Colib.RingTheory.Charpoly.DVRBranchCount",
        }
        for identifier, module in modules.items():
            self.assertEqual(self.library["entries"][identifier]["section"],
                             "charpoly-branches")
            source = (root / (module.replace(".", "/") + ".lean")).read_text()
            self.assertIn(f'colib_tag "{identifier}"', source)
            self.assertIn(module, (root / "Colib.lean").read_text())
        for path in ("scripts/check.sh", ".github/workflows/lean-ci.yml"):
            for module in (
                    "ColibTest.FieldCharpolyPower",
                    "ColibTest.TensorCharpolyProduct",
                    "ColibTest.DVRCharpolyResidue",
                    "ColibTest.IntegralTensorCharpolyProduct",
                    "ColibTest.PolynomialPowerFactorCount",
                    "ColibTest.DVRCharpolyBranchCount",
            ):
                self.assertIn(module, (root / path).read_text())
        self.assertIn("infinite base field", self.library["entries"]["COL-0202"]["scope"])
        self.assertIn("power basis", self.library["entries"]["COL-0204"]["scope"])
        self.assertIn("Characteristic-zero", self.library["entries"]["COL-0207"]["scope"])

    def test_sylow_branch_native_chain_registration(self):
        root = catalog.ROOT
        modules = {
            "COL-0208": "Colib.FieldTheory.SylowFixedField",
            "COL-0209": "Colib.FieldTheory.AdjoinRootSplitBranchEmbedding",
            "COL-0210": "Colib.FieldTheory.PGroupNormalSubfield",
            "COL-0211": "Colib.FieldTheory.PGroupNormalSubfieldEmbedding",
        }
        for identifier, module in modules.items():
            self.assertEqual(self.library["entries"][identifier]["section"],
                             "sylow-field-reduction")
            source = (root / (module.replace(".", "/") + ".lean")).read_text()
            self.assertIn(f'colib_tag "{identifier}"', source)
            self.assertIn(module, (root / "Colib.lean").read_text())
            self.assertNotIn("structure ", source)
            self.assertNotIn("def ", source)
        for path in ("scripts/check.sh", ".github/workflows/lean-ci.yml"):
            for module in (
                    "ColibTest.SylowFixedField",
                    "ColibTest.AdjoinRootSplitBranchEmbedding",
                    "ColibTest.PGroupNormalSubfield",
                    "ColibTest.PGroupNormalSubfieldEmbedding",
            ):
                self.assertIn(module, (root / path).read_text())
        self.assertIn("Zero polynomials", self.library["entries"]["COL-0208"]["scope"])
        self.assertIn("No monicity", self.library["entries"]["COL-0209"]["scope"])
        self.assertIn("original field", self.library["entries"]["COL-0211"]["scope"])

    def test_additivity_keeps_actual_maps_scope_and_tests(self):
        expected = {
            "COL-0213": "geometric-realization",
            "COL-0214": "homotopy-colimits",
            "COL-0215": "homotopy-colimits",
            "COL-0216": "geometric-realization",
            "COL-0217": "homotopy-groups",
            "COL-0218": "waldhausen-k-theory",
            "COL-0219": "waldhausen-k-theory",
            "COL-0220": "geometric-realization",
            "COL-0212": "waldhausen-k-theory",
        }
        for identifier, section in expected.items():
            self.assertEqual(self.library["entries"][identifier]["section"], section)
        self.assertIn("unreversed ordinal join", self.library["entries"]["COL-0216"]["scope"])
        self.assertIn("Infinite-dimensional", self.library["entries"]["COL-0216"]["scope"])
        self.assertIn("No comparison-equivalence or surjectivity assumption",
                      self.library["entries"]["COL-0219"]["scope"])
        self.assertIn("quotient-before-subobject", self.library["entries"]["COL-0219"]["scope"])
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for identifier in expected:
            self.assertTrue(result["entries"][identifier]["references"])
        ledger = json.loads((catalog.ROOT / "docs/migration/waldhausen/additivity.json").read_text())
        self.assertEqual(ledger["source_revision"], "c561118b7795eb9780be9ed391c3251d6a4d0afd")
        self.assertEqual(len(ledger["production_modules"]), 117)
        self.assertFalse((catalog.ROOT /
                          "Colib/CategoryTheory/Waldhausen/Additivity/NormalizeFunctor.lean").exists())
        self.assertIn("independent", self.library["entries"]["COL-0051"]["scope"])
        for test in ledger["tests"]:
            for path in ("scripts/check.sh", ".github/workflows/lean-ci.yml"):
                self.assertIn(test, (catalog.ROOT / path).read_text())

    def native_fixture(self):
        native = {
            "bindings": [],
            "citations": [],
            "stacks": [],
            "declarations": [],
            "modules": [],
        }
        module_names = {
            "sylow-field-reduction": "Colib.FieldTheory.PGroupNormalSubfieldEmbedding",
            "waldhausen-categories": "Colib.CategoryTheory.Waldhausen.Basic",
            "waldhausen-k-theory": "Colib.KTheory.Waldhausen.Basic",
            "homology-colimits": "Colib.Algebra.Category.ModuleCat.FilteredColimits",
            "affine-open-pairs": "Colib.AlgebraicGeometry.Morphisms.OpenImmersion.Pair.Functor",
            "perfect-complexes": "Colib.AlgebraicGeometry.Modules.LocalRepresentativeEquivalence",
            "ext-scalars": "Colib.Algebra.Homology.DerivedCategory.Ext.Quotient",
            "projective-dimension": "Colib.RingTheory.Koszul.Ext",
            "koszul-coefficients": "Colib.RingTheory.Koszul.Coefficients",
            "exact-categories": "Colib.CategoryTheory.ExactCategory.Basic",
            "bicategories": "Colib.CategoryTheory.Bicategory.IsoQuotient",
            "restricted-spans": "Colib.CategoryTheory.QConstruction.Basic",
            "classifying-spaces": "Colib.Topology.ClassifyingSpace.Basic",
            "functor-constructions": "Colib.CategoryTheory.Functor.Rebase",
            "geometric-realization": "Colib.Topology.Realization.FiniteSimplexAdapter",
            "homotopy-groups": "Colib.Topology.Homotopy.HomotopyGroup.Map",
            "homotopy-colimits": "Colib.Topology.Pushout.HomotopyEquivalence",
            "quillen-k-theory": "Colib.KTheory.Quillen.Basic",
            "grothendieck-groups": "Colib.KTheory.GrothendieckGroup.Field",
            "milnor-k-theory": "Colib.KTheory.MilnorK.DegreeTwo",
            "adic-completion": "Colib.RingTheory.AdicCompletion.FiniteAlgebra",
            "principal-euler": "Colib.RingTheory.Multiplicity.PrincipalEuler.Basic",
            "charpoly-branches": "Colib.RingTheory.Charpoly.DVRBranchCount",
            "henselian-ramification": "Colib.RingTheory.Henselian.UniformizerNormalization",
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

    def test_exact_equivalence_keeps_canonical_maps(self):
        item = self.library["entries"]["COL-0179"]
        self.assertEqual(item["section"], "waldhausen-k-theory")
        self.assertIn("canonical KMap", item["statement"])
        self.assertIn("strict chosen-zero preservation is not required", item["scope"])
        self.assertIn("No equality with archived named PerfectK", item["scope"])
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        self.assertTrue(result["entries"]["COL-0179"]["references"])

    def test_perfect_waldhausen_chain_keeps_owners(self):
        self.assertEqual(self.library["entries"]["COL-0177"]["section"], "waldhausen-categories")
        self.assertEqual(self.library["entries"]["COL-0178"]["section"], "perfect-complexes")
        self.assertIn("every relevant pushout apex", self.library["entries"]["COL-0178"]["statement"])
        self.assertIn("not identified literally", self.library["entries"]["COL-0178"]["scope"])
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for identifier in ("COL-0177", "COL-0178"):
            self.assertTrue(result["entries"][identifier]["references"])

    def test_perfect_local_comparison_keeps_exact_scope(self):
        item = self.library["entries"]["COL-0176"]
        self.assertEqual(item["section"], "perfect-complexes")
        self.assertEqual(item["kind"], "comparison")
        self.assertIn("arbitrary supplied universe d", item["scope"])
        self.assertIn("No global strict representative", item["scope"])
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        self.assertTrue(result["entries"]["COL-0176"]["references"])
        self.assertEqual(
            result["sections"]["perfect-complexes"]["modules"],
            ["Colib.AlgebraicGeometry.Modules.LocalRepresentativeEquivalence"],
        )

    def test_waldhausen_homotopy_chain_keeps_model_and_owners(self):
        self.assertEqual(self.library["entries"]["COL-0154"]["section"], "waldhausen-categories")
        for number in range(155, 159):
            self.assertEqual(
                self.library["entries"][f"COL-{number:04d}"]["section"], "waldhausen-k-theory"
            )
        self.assertIn("unnormalized", self.library["entries"]["COL-0146"]["scope"])
        self.assertIn("strict chosen-zero", self.library["entries"]["COL-0154"]["scope"])
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for number in range(154, 159):
            self.assertTrue(result["entries"][f"COL-{number:04d}"]["references"])

    def test_three_route_chains_keep_grouped_owners(self):
        for identifier, section in (
            ("COL-0144", "waldhausen-categories"),
            ("COL-0145", "waldhausen-categories"),
            ("COL-0146", "waldhausen-categories"),
            ("COL-0147", "homology-colimits"),
            ("COL-0148", "homology-colimits"),
            ("COL-0149", "affine-open-pairs"),
        ):
            self.assertEqual(self.library["entries"][identifier]["section"], section)
        catalog.compile_library(self.library, self.native_fixture(), {}, "main")

    def test_nerve_cylinder_and_finite_simplex_ids_keep_their_owners(self):
        for identifier, section in (
            ("COL-0058", "classifying-spaces"),
            ("COL-0059", "geometric-realization"),
        ):
            self.assertEqual(self.library["entries"][identifier]["section"], section)
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        self.assertEqual(
            result["sections"]["geometric-realization"]["modules"],
            ["Colib.Topology.Realization.FiniteSimplexAdapter"],
        )
        for identifier in ("COL-0058", "COL-0059"):
            self.assertTrue(result["entries"][identifier]["references"])

    def test_realization_prerequisite_ids_keep_their_owners(self):
        for index in range(60, 65):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"],
                "geometric-realization",
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(60, 65):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_finite_prism_id_keeps_its_owner(self):
        self.assertEqual(
            self.library["entries"]["COL-0065"]["section"], "geometric-realization"
        )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        self.assertTrue(result["entries"]["COL-0065"]["references"])

    def test_realized_standard_prism_ids_keep_their_owners(self):
        for identifier in ("COL-0066", "COL-0067"):
            self.assertEqual(
                self.library["entries"][identifier]["section"], "geometric-realization"
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for identifier in ("COL-0066", "COL-0067"):
            self.assertTrue(result["entries"][identifier]["references"])

    def test_realization_bridge_ids_keep_their_owners(self):
        for index in range(68, 71):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"],
                "geometric-realization",
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(68, 71):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_based_invariance_and_kmap_composition_ids_keep_their_owners(self):
        for identifier, section in (
            ("COL-0071", "homotopy-groups"),
            ("COL-0072", "quillen-k-theory"),
        ):
            self.assertEqual(self.library["entries"][identifier]["section"], section)
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for identifier in ("COL-0071", "COL-0072"):
            self.assertTrue(result["entries"][identifier]["references"])

    def test_split_kernel_and_q_object_class_ids_keep_their_owners(self):
        for index in range(73, 76):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"], "exact-categories"
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(73, 76):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_algebraic_q_groupoid_ids_keep_their_owners(self):
        for index in range(76, 81):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"],
                "exact-categories" if index < 78 else "grothendieck-groups",
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(76, 81):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_object_loop_bridge_ids_keep_their_owners(self):
        for index in range(81, 87):
            section = (
                "geometric-realization" if index < 84 else
                "classifying-spaces" if index < 86 else "grothendieck-groups"
            )
            self.assertEqual(self.library["entries"][f"COL-{index:04d}"]["section"], section)
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(81, 87):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_open_cover_and_sequential_colimit_ids_keep_their_owners(self):
        for index in range(87, 90):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"], "homotopy-groups"
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(87, 90):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_constant_realization_and_completion_ids_keep_their_owners(self):
        for index in range(90, 94):
            section = "geometric-realization" if index < 92 else "classifying-spaces"
            self.assertEqual(self.library["entries"][f"COL-{index:04d}"]["section"], section)
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(90, 94):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_pushout_and_open_cover_full_ids_keep_their_owners(self):
        for index in range(94, 98):
            section = "functor-constructions" if index == 96 else "homotopy-groups"
            self.assertEqual(self.library["entries"][f"COL-{index:04d}"]["section"], section)
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(94, 98):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_simplex_boundary_and_collar_ids_keep_their_owners(self):
        for index in range(98, 100):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"],
                "geometric-realization",
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(98, 100):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_simplex_charts_and_annulus_ids_keep_their_owners(self):
        for index in range(100, 102):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"],
                "geometric-realization",
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(100, 102):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_simplex_attachment_collar_ids_keep_their_owners(self):
        for index in range(102, 104):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"],
                "geometric-realization",
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(102, 104):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_attachment_cover_generation_fullness_ids_keep_their_owners(self):
        for index in range(104, 107):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"],
                "geometric-realization",
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(104, 107):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_boundary_endpoints_and_graph_anchors_ids_keep_their_owners(self):
        for index in range(107, 109):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"],
                "geometric-realization",
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(107, 109):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

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

    def test_q_functoriality_ids_keep_their_owners(self):
        self.assertEqual(self.library["entries"]["COL-0036"]["section"], "restricted-spans")
        self.assertEqual(self.library["entries"]["COL-0037"]["section"], "exact-categories")
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for identifier in ("COL-0036", "COL-0037"):
            self.assertTrue(result["entries"][identifier]["references"])

    def test_q_connectedness_ids_keep_their_owners(self):
        for index in (38, 39, 40):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"],
                "exact-categories",
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in (38, 39, 40):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_quillen_homotopy_ids_keep_their_owners(self):
        owners = {43: "classifying-spaces", 44: "restricted-spans", 45: "quillen-k-theory"}
        for index, section in owners.items():
            self.assertEqual(self.library["entries"][f"COL-{index:04d}"]["section"], section)
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in owners:
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_q_core_ids_keep_their_owners(self):
        self.assertEqual(self.library["entries"]["COL-0046"]["section"], "restricted-spans")
        for index in range(47, 51):
            self.assertEqual(
                self.library["entries"][f"COL-{index:04d}"]["section"], "exact-categories"
            )
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in range(46, 51):
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_quillen_map_ids_keep_their_owners(self):
        owners = {
            51: "functor-constructions", 52: "homotopy-groups",
            53: "classifying-spaces", 54: "classifying-spaces", 55: "quillen-k-theory",
        }
        for index, section in owners.items():
            self.assertEqual(self.library["entries"][f"COL-{index:04d}"]["section"], section)
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for index in owners:
            self.assertTrue(result["entries"][f"COL-{index:04d}"]["references"])

    def test_normalized_q_ids_keep_their_owners(self):
        self.assertEqual(self.library["entries"]["COL-0056"]["section"], "functor-constructions")
        self.assertEqual(self.library["entries"]["COL-0057"]["section"], "exact-categories")
        result = catalog.compile_library(self.library, self.native_fixture(), {}, "main")
        for identifier in ("COL-0056", "COL-0057"):
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
