/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.KTheory.Quillen.Devissage.Basic
public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.Topology.ClassifyingSpace.Devissage
public import Colib.CategoryTheory.Abelian.Devissage.CommaLayers
public import Colib.CategoryTheory.TheoremA.ContractibleComma
public import Colib.KTheory.Quillen.Map.HomotopyEquivalence

/-!
# Homotopical Quillen dévissage

For a small abelian category, the classical subobject, quotient, and
finite-product hypotheses and actual finite filtrations imply that the
canonical Q-inclusion is a homotopy equivalence. The proof identifies each
comma category with the poset of layers, contracts it by intersection and
finite-filtration induction, and applies the proved Quillen Theorem A.

Both the ordinary inclusion and its canonically zero-rebased version are
retained as exact forward maps. The all-degree K-group isomorphisms use the proved homotopy-group
invariance
theorem, without assuming based inverse homotopies.
-/
/-!
Implementation provenance: adapted from
`Quillen/Devissage/Homotopical.lean` at Quillen
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
Native Mathlib full subcategories, Colib exact structures,
restricted spans, actual realization maps and their universes are retained.
No extension-closure, uniform filtration bound, alternate K-model or Aglib import is added.
-/

@[expose] public section

open CategoryTheory.ExactCategory
open CategoryTheory.ObjectProperty


noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory.Abelian.Devissage
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [SmallCategory C] [Abelian C]
  (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderSubobjects]
  [P.IsClosedUnderQuotients] [P.IsClosedUnderFiniteProducts]

/-- The actual inclusion comma categories are contractible under the classical
finite-filtration hypothesis. -/
theorem qComma_contractible (h : FiltrationHypothesis P) (M : C) :
    ContractibleSpace (ClassifyingSpace (QComma P M)) := by
  obtain ⟨F⟩ := h M
  let := Layer.contractible_of_filtration F
  exact (equivalenceClassifyingHomotopyEquiv (layerCommaEquivalence P M)).symm.contractibleSpace

/-- Classical Quillen dévissage, with the canonical realized Q-inclusion as
the forward map. No extension closure or uniform filtration bound is assumed. -/
def classifyingHomotopyEquiv (h : FiltrationHypothesis P) :
    ContinuousMap.HomotopyEquiv
      (ClassifyingSpace (QConstruction (abelianExactStructure P.FullSubcategory).deflation
        (abelianExactStructure P.FullSubcategory).inflation))
      (ClassifyingSpace (QConstruction (abelianExactStructure C).deflation
        (abelianExactStructure C).inflation)) :=
  TheoremA.contractibleCommaClassifyingHomotopyEquiv (mapQ P)
    (fun M => qComma_contractible P h M.obj.of)

@[simp]
theorem classifyingHomotopyEquiv_toFun (h : FiltrationHypothesis P) :
    (classifyingHomotopyEquiv P h).toFun = (classifyingSpaceMap (mapQ P)).hom := rfl

/-- The actual pointed continuous map used in the project's inclusion-induced
Quillen K-group homomorphisms. -/
def pointedClassifyingMap :=
  (classifyingSpaceMap (exactInclusion P).normalizedQ).hom

/-- Rebasing at the chosen zero object preserves the proved equivalence.
Its forward map is precisely the one defining `Devissage.KMap`. -/
def pointedClassifyingHomotopyEquiv (h : FiltrationHypothesis P) :
    ContinuousMap.HomotopyEquiv
      (ClassifyingSpace (QConstruction (abelianExactStructure P.FullSubcategory).deflation
        (abelianExactStructure P.FullSubcategory).inflation))
      (ClassifyingSpace (QConstruction (abelianExactStructure C).deflation
        (abelianExactStructure C).inflation)) :=
  TheoremA.homotopyEquivWithMap (classifyingHomotopyEquiv P h)
    (pointedClassifyingMap P)
    ⟨classifyingSpaceNaturalTransformationHomotopy
      (rebaseFunctorIso (mapQ P)
        (QConstruction.of (abelianExactStructure P.FullSubcategory).deflation
          (abelianExactStructure P.FullSubcategory).inflation (0 : P.FullSubcategory))
        (QConstruction.of (abelianExactStructure C).deflation
          (abelianExactStructure C).inflation (0 : C))
        ((abelianExactStructure C).qIsoOfIso (exactInclusion P).toFunctor.mapZeroObject)).inv⟩

@[simp]
theorem pointedClassifyingHomotopyEquiv_toFun (h : FiltrationHypothesis P) :
    (pointedClassifyingHomotopyEquiv P h).toFun = pointedClassifyingMap P := rfl

/-- The canonical rebased inclusion preserves the actual K-theory basepoints. -/
lemma pointedClassifyingMap_basepoint :
    pointedClassifyingMap P (abelianExactStructure P.FullSubcategory).kBasepoint =
      (abelianExactStructure C).kBasepoint :=
  (exactInclusion P).normalizedQ_map_point

/-- Classical dévissage on every nonnegative Quillen K-group. The inverse is
obtained from the proved homotopy equivalence, not postulated as filtration data. -/
def KEquiv (h : FiltrationHypothesis P) (n : ℕ) :
    (abelianExactStructure P.FullSubcategory).K n ≃* (abelianExactStructure C).K n :=
  (exactInclusion P).KEquivOfHomotopyEquiv (pointedClassifyingHomotopyEquiv P h) rfl n

/-- The forward homomorphism of dévissage is exactly the already-defined
inclusion-induced K-map, including its canonical zero-object rebasing. -/
@[simp] theorem KEquiv_coe (h : FiltrationHypothesis P) (n : ℕ) :
    (↑(KEquiv P h n) : (abelianExactStructure P.FullSubcategory).K n →*
      (abelianExactStructure C).K n) =
        KMap P n := rfl

/-- In particular the canonical inclusion-induced map is bijective in every
degree, including `K₀ = π₁ BQ`. -/
theorem KMap_bijective (h : FiltrationHypothesis P) (n : ℕ) :
    Function.Bijective (KMap P n) := (KEquiv P h n).bijective

end CategoryTheory.Abelian.Devissage

attribute [colib_tag "COL-0246",
  colib_ref "WeibelKBook" "V, Devissage Theorem 4.1 and proof, page 33" "adaptation"
    "Classical homotopical devissage with the actual Q-inclusion and canonical inclusion KMap"]
  CategoryTheory.Abelian.Devissage.classifyingHomotopyEquiv
  CategoryTheory.Abelian.Devissage.classifyingHomotopyEquiv_toFun
  CategoryTheory.Abelian.Devissage.pointedClassifyingHomotopyEquiv
  CategoryTheory.Abelian.Devissage.KEquiv
  CategoryTheory.Abelian.Devissage.KEquiv_coe
  CategoryTheory.Abelian.Devissage.KMap_bijective

attribute [colib_ref "Quillen1973"
    "Section 5, Theorem 4, p. 112" "adaptation"
    "Abelian devissage with subobject, quotient and finite-product closure and finite filtrations"]
  CategoryTheory.Abelian.Devissage.classifyingHomotopyEquiv
  CategoryTheory.Abelian.Devissage.KEquiv
  CategoryTheory.Abelian.Devissage.KMap_bijective
