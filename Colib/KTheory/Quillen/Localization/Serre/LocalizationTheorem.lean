/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Quillen.Localization.Serre.FiberEquivalence
public import Colib.KTheory.Quillen.Localization.Serre.FiberBoundary
public import Colib.KTheory.Quillen.Localization.Serre.KZero

/-!
# The canonical connective Serre localization sequence

For a small abelian category and a Serre class, the proved canonical based
fiber comparison identifies the native path-space long exact sequence with
K-theory of the Serre subcategory, ambient category and canonical quotient.
The boundary is the actual path-space boundary followed by the inverse of the
proved comparison group isomorphism. Inclusion and quotient maps are unchanged.
No comparison, filtration, cartesian or quotient hypothesis is added.

Adapted from `Quillen/Localization/Serre/LocalizationTheorem.lean`,
`LocalizationEndpoint.lean` and `LocalizationLESAdapter.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Conditional transport interfaces are
eliminated: every exactness proof uses the actual proved comparison directly.
The terminal K-zero surjection reuses the independent canonical K-zero theorem.
-/

@[expose] public noncomputable section

universe u
open CategoryTheory CategoryTheory.Limits Topology

namespace CategoryTheory.ExactCategory.SerreLocalization

attribute [local instance] Abelian.hasFiniteBiproducts canonicalQuotientAbelian

variable {C : Type u} [Category.{u} C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass]

/-- The actual localization boundary, including K₁(C/P) → K₀(P). -/
def connectingHom (n : ℕ) :
    (abelianExactStructure P.isoModSerre.Localization).K (n + 1) →*
      (abelianExactStructure P.FullSubcategory).K n :=
  (localizationFiberEquiv P n).symm.toMonoidHom.comp (fiberConnectingHom P n)

/-- The comparison identifies the boundary with the native path-space boundary. -/
theorem comparison_comp_connectingHom (n : ℕ) :
    (localizationFiberComparisonHom P n).comp (connectingHom P n) =
      fiberConnectingHom P n := by
  ext a
  exact (localizationFiberEquiv P n).apply_symm_apply (fiberConnectingHom P n a)

/-- Exactness at the actual ambient K-group in every nonnegative degree. -/
theorem inclusion_range_eq_quotient_ker (n : ℕ) :
    (Abelian.Devissage.KMap P n).range = (quotientKMap P n).ker := by
  rw [← fiberProjection_range_eq_quotient_ker P n,
    ← localizationFiberComparisonHom_projection P n]
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨b, rfl⟩
    obtain ⟨c, rfl⟩ := (localizationFiberComparisonHom_bijective P n).surjective b
    exact ⟨c, rfl⟩

/-- Exactness at the actual quotient K-group in every positive degree. -/
theorem quotient_range_eq_connecting_ker (n : ℕ) :
    (quotientKMap P (n + 1)).range = (connectingHom P n).ker := by
  rw [quotient_range_eq_fiberConnecting_ker]
  ext a
  change fiberConnectingHom P n a = 1 ↔
    (localizationFiberEquiv P n).symm (fiberConnectingHom P n a) = 1
  exact (map_eq_one_iff (localizationFiberEquiv P n).symm
    (localizationFiberEquiv P n).symm.injective).symm

/-- Exactness at the Serre-subcategory K-group in every nonnegative degree. -/
theorem connecting_range_eq_inclusion_ker (n : ℕ) :
    (connectingHom P n).range = (Abelian.Devissage.KMap P n).ker := by
  have hp (a : (abelianExactStructure P.FullSubcategory).K n) :
      localizationFiberProjectionHom P n (localizationFiberEquiv P n a) =
        Abelian.Devissage.KMap P n a :=
    DFunLike.congr_fun (localizationFiberComparisonHom_projection P n) a
  ext a
  change (∃ b, (localizationFiberEquiv P n).symm (fiberConnectingHom P n b) = a) ↔
    Abelian.Devissage.KMap P n a = 1
  constructor
  · rintro ⟨b, rfl⟩
    rw [← hp, MulEquiv.apply_symm_apply]
    have hm : fiberConnectingHom P n b ∈ (fiberConnectingHom P n).range := ⟨b, rfl⟩
    rw [fiberConnecting_range_eq_projection_ker] at hm
    exact hm
  · intro ha
    have hm : localizationFiberEquiv P n a ∈ (localizationFiberProjectionHom P n).ker :=
      (hp a).trans ha
    rw [← fiberConnecting_range_eq_projection_ker] at hm
    obtain ⟨b, hb⟩ := hm
    exact ⟨b, (congrArg (localizationFiberEquiv P n).symm hb).trans
      ((localizationFiberEquiv P n).symm_apply_apply a)⟩

/-- The boundary is uniquely determined by its equation with the actual comparison. -/
theorem connecting_unique (n : ℕ)
    (δ : (abelianExactStructure P.isoModSerre.Localization).K (n + 1) →*
      (abelianExactStructure P.FullSubcategory).K n)
    (hδ : (localizationFiberComparisonHom P n).comp δ = fiberConnectingHom P n) :
    δ = connectingHom P n := by
  ext a
  apply (localizationFiberComparisonHom_bijective P n).injective
  exact DFunLike.congr_fun (hδ.trans (comparison_comp_connectingHom P n).symm) a

/-- The full connective sequence, with inclusion and quotient fixed to the original K-maps. -/
structure KLocalizationSequence where
  /-- The boundary from the actual Serre quotient in degree `n + 1`. -/
  connecting : ∀ n : ℕ, (abelianExactStructure P.isoModSerre.Localization).K (n + 1) →*
    (abelianExactStructure P.FullSubcategory).K n
  /-- The boundary has the prescribed path-space interpretation. -/
  comparison_connecting : ∀ n,
    (localizationFiberComparisonHom P n).comp (connecting n) = fiberConnectingHom P n
  /-- Exactness at the original ambient term. -/
  exact_ambient : ∀ n, (Abelian.Devissage.KMap P n).range = (quotientKMap P n).ker
  /-- Exactness at the original quotient term. -/
  exact_quotient : ∀ n, (quotientKMap P (n + 1)).range = (connecting n).ker
  /-- Exactness at the original Serre-subcategory term. -/
  exact_subcategory : ∀ n, (connecting n).range = (Abelian.Devissage.KMap P n).ker
  /-- The connective sequence terminates at the canonical K-zero surjection. -/
  surjective_KZero : Function.Surjective (quotientKMap P 0)

/-- The proved canonical localization sequence, without any comparison hypotheses. -/
def localizationSequence : KLocalizationSequence P where
  connecting := connectingHom P
  comparison_connecting := comparison_comp_connectingHom P
  exact_ambient := inclusion_range_eq_quotient_ker P
  exact_quotient := quotient_range_eq_connecting_ker P
  exact_subcategory := connecting_range_eq_inclusion_ker P
  surjective_KZero := quotientKZero_surjective P

@[simp]
theorem localizationSequence_connecting (n : ℕ) :
    (localizationSequence P).connecting n = connectingHom P n := rfl

/-- All recurring exactness positions and the connective K-zero endpoint. -/
theorem localization_longExact :
    (∀ n, (Abelian.Devissage.KMap P n).range = (quotientKMap P n).ker) ∧
    (∀ n, (quotientKMap P (n + 1)).range = (connectingHom P n).ker) ∧
    (∀ n, (connectingHom P n).range = (Abelian.Devissage.KMap P n).ker) ∧
    Function.Surjective (quotientKMap P 0) :=
  ⟨inclusion_range_eq_quotient_ker P, quotient_range_eq_connecting_ker P,
    connecting_range_eq_inclusion_ker P, quotientKZero_surjective P⟩

/-- The low-degree tail K₁(C) → K₁(C/P) → K₀(P) → K₀(C) → K₀(C/P) → 0. -/
theorem localization_KZero_tail :
    (quotientKMap P 1).range = (connectingHom P 0).ker ∧
    (connectingHom P 0).range = (Abelian.Devissage.KMap P 0).ker ∧
    (Abelian.Devissage.KMap P 0).range = (quotientKMap P 0).ker ∧
    Function.Surjective (quotientKMap P 0) :=
  ⟨quotient_range_eq_connecting_ker P 0, connecting_range_eq_inclusion_ker P 0,
    inclusion_range_eq_quotient_ker P 0, quotientKZero_surjective P⟩

end CategoryTheory.ExactCategory.SerreLocalization

attribute [colib_ref "WeibelKBook" "V, Theorem 5.1, page 35" "adaptation"
  "Canonical connective Serre localization with original K-maps and path-space boundary"]
  CategoryTheory.ExactCategory.SerreLocalization.localizationSequence
  CategoryTheory.ExactCategory.SerreLocalization.localization_longExact
  CategoryTheory.ExactCategory.SerreLocalization.localization_KZero_tail

attribute [colib_tag "COL-0250"]
  CategoryTheory.ExactCategory.SerreLocalization.connectingHom
  CategoryTheory.ExactCategory.SerreLocalization.comparison_comp_connectingHom
  CategoryTheory.ExactCategory.SerreLocalization.connecting_unique
  CategoryTheory.ExactCategory.SerreLocalization.inclusion_range_eq_quotient_ker
  CategoryTheory.ExactCategory.SerreLocalization.quotient_range_eq_connecting_ker
  CategoryTheory.ExactCategory.SerreLocalization.connecting_range_eq_inclusion_ker
  CategoryTheory.ExactCategory.SerreLocalization.KLocalizationSequence
  CategoryTheory.ExactCategory.SerreLocalization.localizationSequence
  CategoryTheory.ExactCategory.SerreLocalization.localizationSequence_connecting
  CategoryTheory.ExactCategory.SerreLocalization.localization_longExact
  CategoryTheory.ExactCategory.SerreLocalization.localization_KZero_tail

attribute [colib_ref "Quillen1973"
    "Section 5, Theorem 5, p. 113" "adaptation"
    "Connective Serre localization through the surjective K-zero endpoint, retaining the actual \
      maps and boundary"]
  CategoryTheory.ExactCategory.SerreLocalization.localizationSequence
  CategoryTheory.ExactCategory.SerreLocalization.localization_longExact
  CategoryTheory.ExactCategory.SerreLocalization.localization_KZero_tail
