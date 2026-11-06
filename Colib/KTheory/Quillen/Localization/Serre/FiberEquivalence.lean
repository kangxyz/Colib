/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Quillen.Localization.Serre.NormalizedBasepoint
public import Colib.CategoryTheory.TheoremB.StructuredWeakComparison
public import Colib.CategoryTheory.TheoremB.StructuredFullWeakComparison

/-!
# The canonical Serre-localization fiber comparison

The actual normalized structured-comma equivalence, the proved quotient transitions and
Quillen's Theorem B identify the original based localization comparison on every homotopy
set, including degree zero. The full two-parameter coherence fixes its prescribed basepoint.
The resulting group equivalence retains exactly the original comparison homomorphism.

Implementation provenance: the unconditional endpoints of
`Quillen/Localization/Serre/LocalizationTheorem.lean` and the exact-map proof in
`Quillen/Localization/Serre/StructuredComparisonWeak.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The proof directly uses native Theorem B;
no conditional localization adapter or global homotopy inverse is assumed.
-/

@[expose] public noncomputable section

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory Topology
open scoped ZeroObject
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory.ExactCategory.SerreLocalization
attribute [local instance] Abelian.hasFiniteBiproducts canonicalQuotientAbelian
variable {C : Type u} [Category.{u} C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass]

/-- The original based comparison induces a bijection on every finite homotopy set,
including π₀, under only the canonical Serre-localization hypotheses. -/
theorem basedLocalizationFiberComparison_bijective (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin n)
      (basedLocalizationFiberComparison P) (basedLocalizationFiberComparison_basepoint P)) := by
  have h₁ := homotopyGroupMap_bijective_of_homotopyEquiv
    (normalizedZeroStructuredCommaClassifyingHomotopyEquiv P)
    (normalizedSerreToZeroStructuredComma_map_basepoint P) n
  have h₂ (d : (abelianExactStructure P.isoModSerre.Localization).QCategory)
      (hd : (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ.obj
        (abelianExactStructure C).qZero = d) :
      Function.Bijective (HomotopyGroup.map (N := Fin n)
        (TheoremB.structuredFiberComparison
          (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ d)
        (TheoremB.structuredFiberComparison_identity_of_eq
          (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ
          (abelianExactStructure C).qZero d hd)) := by
    subst d
    exact TheoremB.structuredFiberComparison_bijective
      (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ
      (normalizedQuotient_structuredTransitions P) (abelianExactStructure C).qZero n
  have hcomp := homotopyGroupMap_bijective_comp
    (classifyingSpaceMap (normalizedSerreToZeroStructuredComma P)).hom
    (TheoremB.structuredFiberComparison
      (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ
      (abelianExactStructure P.isoModSerre.Localization).qZero)
    (normalizedSerreToZeroStructuredComma_map_basepoint P)
    (TheoremB.structuredFiberComparison_identity_of_eq
      (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ
      (abelianExactStructure C).qZero
      (abelianExactStructure P.isoModSerre.Localization).qZero (quotientNormalized_obj_zero P)) n
    h₁ (h₂ _ (quotientNormalized_obj_zero P))
  exact homotopyGroupMap_bijective_of_based_homotopy
    (normalizedStructuredFiberComparison_basepoint P)
    (basedLocalizationFiberComparison_basepoint P)
    (normalizedStructuredFiberComparisonHomotopy P).symm
    (fun t ↦ normalizedStructuredFiberComparisonHomotopy_based P (unitInterval.symm t)) n hcomp

/-- Bijectivity of the actual comparison homomorphism in K-degree `n`. -/
theorem localizationFiberComparisonHom_bijective (n : ℕ) :
    Function.Bijective (localizationFiberComparisonHom P n) :=
  basedLocalizationFiberComparison_bijective P (n + 1)

/-- The canonical Serre-localization group equivalence, constructed from the actual
comparison homomorphism rather than from a separately chosen homotopy equivalence. -/
def localizationFiberEquiv (n : ℕ) :
    (abelianExactStructure P.FullSubcategory).K n ≃*
      HomotopyGroup.Pi (n + 1) (NormalizedLocalizationFiber P) (normalizedFiberBasepoint P) :=
  MulEquiv.ofBijective (localizationFiberComparisonHom P n)
    (localizationFiberComparisonHom_bijective P n)

/-- The equivalence's forward homomorphism is exactly the original comparison. -/
@[simp] theorem localizationFiberEquiv_coe (n : ℕ) :
    (↑(localizationFiberEquiv P n) : (abelianExactStructure P.FullSubcategory).K n →*
      HomotopyGroup.Pi (n + 1) (NormalizedLocalizationFiber P) (normalizedFiberBasepoint P)) =
        localizationFiberComparisonHom P n := rfl

/-- The same original comparison is a weak homotopy equivalence on every component
and at every basepoint. This does not assert a chosen continuous homotopy inverse. -/
theorem basedLocalizationFiberComparison_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence (basedLocalizationFiberComparison P) := by
  have h := (TheoremB.structuredFiberComparison_isWeakHomotopyEquivalence
    (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ
    (normalizedQuotient_structuredTransitions P)
    (abelianExactStructure P.isoModSerre.Localization).qZero).comp
      (isWeakHomotopyEquivalence_of_homotopyEquiv
        (normalizedZeroStructuredCommaClassifyingHomotopyEquiv P))
  exact h.of_homotopy (normalizedStructuredFiberComparisonHomotopy P).symm

attribute [colib_ref "WeibelKBook" "V, Theorem 5.1 and proof, page 35" "adaptation"
  "The canonical Serre-localization comparison is a weak equivalence, retaining every based map"]
  basedLocalizationFiberComparison_bijective
  localizationFiberComparisonHom_bijective
  localizationFiberEquiv
  basedLocalizationFiberComparison_isWeakHomotopyEquivalence

end CategoryTheory.ExactCategory.SerreLocalization

namespace CategoryTheory.ExactCategory.SerreLocalization

attribute [colib_tag "COL-0249"]
  basedLocalizationFiberComparison_bijective
  localizationFiberComparisonHom_bijective
  localizationFiberEquiv
  localizationFiberEquiv_coe
  basedLocalizationFiberComparison_isWeakHomotopyEquivalence

end CategoryTheory.ExactCategory.SerreLocalization
