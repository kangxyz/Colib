/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Quillen.Localization.Serre.LocalizationTheorem
public import Colib.KTheory.Quillen.Equivalence
public import Colib.KTheory.Quillen.Map.Functoriality

/-!
# Localization sequences with the actual target category

An additive functor presenting a Serre quotient is allowed to have an actual
small abelian target, rather than the formal category of fractions. Its
localization property constructs an equivalence from that formal quotient.
The strict factorization of the construction lift identifies the induced
K-map with the original exact functor's K-map, without any assumed comparison
on K-theory. Transporting the canonical path-space boundary then gives all
three exactness positions and the surjective connective K₀ endpoint.

Adapted from `Quillen/Localization/Serre/LocalizationTarget.lean` at Quillen
commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual construction lift,
strict factorization, equivalence-induced K-map, path-space boundary, and
small source/target universe and Serre hypotheses are retained.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ExactCategory.SerreLocalization

attribute [local instance] Abelian.hasFiniteBiproducts canonicalQuotientAbelian

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Abelian C] [Abelian D] (P : ObjectProperty C) [P.IsSerreClass]
  (L : C ⥤ D) [L.IsLocalization P.isoModSerre] [L.Additive]

/-- The actual functor from the formal quotient, constructed from the
localization universal property. -/
def targetLift : P.isoModSerre.Localization ⥤ D :=
  Localization.Construction.lift L (Localization.inverts L P.isoModSerre)

omit [Abelian D] [L.Additive] in
/-- This lift factors the specified functor strictly. -/
@[simp] theorem targetLift_fac : P.isoModSerre.Q ⋙ targetLift P L = L :=
  Localization.Construction.fac _ _

instance targetLift_isEquivalence : (targetLift P L).IsEquivalence := by
  dsimp [targetLift]
  infer_instance

instance targetLift_additive : (targetLift P L).Additive := by
  apply (Localization.functor_additive_iff P.isoModSerre.Q P.isoModSerre _).2
  rw [targetLift_fac]
  infer_instance

/-- The equivalence to the actual target is exact for the standard abelian
exact structures. -/
def targetLiftExactFunctor :
    ExactFunctor (abelianExactStructure P.isoModSerre.Localization)
      (abelianExactStructure D) where
  toFunctor := targetLift P L
  map_conflation _ hS := hS.map_of_exact _

/-- Equality of the underlying functors gives strict equality of these exact
functors, since the remaining fields express properties. -/
theorem quotient_comp_targetLift :
    (ExactFunctor.serreLocalization P P.isoModSerre.Q).comp
      (targetLiftExactFunctor P L) = ExactFunctor.serreLocalization P L := by
  have h : ((ExactFunctor.serreLocalization P P.isoModSerre.Q).comp
      (targetLiftExactFunctor P L)).toFunctor =
        (ExactFunctor.serreLocalization P L).toFunctor := targetLift_fac P L
  generalize (ExactFunctor.serreLocalization P P.isoModSerre.Q).comp
    (targetLiftExactFunctor P L) = F at *
  generalize ExactFunctor.serreLocalization P L = G at *
  have h' : F.toFunctor = G.toFunctor := h
  cases F
  cases G
  cases h'
  rfl

instance targetLiftExactFunctor_mapQ_isEquivalence :
    (targetLiftExactFunctor P L).mapQ.IsEquivalence := by
  let : (targetLiftExactFunctor P L).toFunctor.IsEquivalence :=
    targetLift_isEquivalence P L
  apply ExactFunctor.mapQ_isEquivalence_of_equivalence
  · intro X Y f hf
    apply (abelianExactStructure_inflation_iff _ _).2
    exact (targetLift P L).mono_of_mono_map
      ((abelianExactStructure_inflation_iff _ _).1 hf)
  · intro X Y f hf
    apply (abelianExactStructure_deflation_iff _ _).2
    exact (targetLift P L).epi_of_epi_map
      ((abelianExactStructure_deflation_iff _ _).1 hf)

/-- The genuine categorical equivalence induces this K-equivalence. Its
forward map is precisely the canonical K-map of the quotient lift. -/
def targetKEquiv (n : ℕ) :
    (abelianExactStructure P.isoModSerre.Localization).K n ≃* (abelianExactStructure D).K n :=
  (targetLiftExactFunctor P L).KEquivOfMapQIsEquivalence n

/-- The underlying monoid homomorphism of this K-equivalence. -/
@[simp] theorem targetKEquiv_coe (n : ℕ) :
    (↑(targetKEquiv P L n) : (abelianExactStructure P.isoModSerre.Localization).K n →*
      (abelianExactStructure D).K n) =
        (targetLiftExactFunctor P L).KMap n := rfl

/-- Strict factorization and proved K-functoriality identify the transported
quotient map with the K-map of the original localization functor. -/
theorem targetKEquiv_comp_quotientKMap (n : ℕ) :
    (targetKEquiv P L n).toMonoidHom.comp (quotientKMap P n) = KMap P L n := by
  change ((targetLiftExactFunctor P L).KMap n).comp
    ((ExactFunctor.serreLocalization P P.isoModSerre.Q).KMap n) = _
  rw [← ExactFunctor.KMap_comp, quotient_comp_targetLift]
  rfl

@[simp] theorem targetKEquiv_apply_quotientKMap (n : ℕ)
    (x : (abelianExactStructure C).K n) :
    targetKEquiv P L n (quotientKMap P n x) = KMap P L n x :=
  congrArg (fun f : (abelianExactStructure C).K n →* (abelianExactStructure D).K n => f x)
    (targetKEquiv_comp_quotientKMap P L n)

/-- The connecting map into the Serre subcategory, obtained by transporting
the genuine canonical path-space boundary along the constructed equivalence. -/
def actualConnectingHom (n : ℕ) :
    (abelianExactStructure D).K (n + 1) →*
      (abelianExactStructure P.FullSubcategory).K n :=
  (connectingHom P n).comp (targetKEquiv P L (n + 1)).symm.toMonoidHom

/-- The transported boundary is exactly the canonical boundary under the
specified target equivalence. -/
@[simp] theorem actualConnectingHom_comp_targetLiftKMap (n : ℕ) :
    (actualConnectingHom P L n).comp ((targetLiftExactFunctor P L).KMap (n + 1)) =
      connectingHom P n := by
  ext x
  change (connectingHom P n) ((targetKEquiv P L (n + 1)).symm
    (((targetLiftExactFunctor P L).KMap (n + 1)) x)) = _
  have hx := DFunLike.congr_fun (targetKEquiv_coe P L (n + 1)) x
  change (targetKEquiv P L (n + 1)) x = _ at hx
  rw [← hx, MulEquiv.symm_apply_apply]

/-- Comparison with the original path-space connecting homomorphism. -/
theorem comparison_comp_actualConnectingHom (n : ℕ) :
    (localizationFiberComparisonHom P n).comp (actualConnectingHom P L n) =
      (fiberConnectingHom P n).comp (targetKEquiv P L (n + 1)).symm.toMonoidHom := by
  rw [actualConnectingHom, ← MonoidHom.comp_assoc, comparison_comp_connectingHom]

/-- Exactness at the original source K-group in every nonnegative degree. -/
theorem actual_inclusion_range_eq_KMap_ker (n : ℕ) :
    (Abelian.Devissage.KMap P n).range = (KMap P L n).ker := by
  rw [inclusion_range_eq_quotient_ker]
  ext x
  change quotientKMap P n x = 1 ↔ KMap P L n x = 1
  rw [← targetKEquiv_apply_quotientKMap]
  exact (map_eq_one_iff (targetKEquiv P L n) (targetKEquiv P L n).injective).symm

/-- Exactness at the actual target K-group in every positive degree. -/
theorem actual_KMap_range_eq_connecting_ker (n : ℕ) :
    (KMap P L (n + 1)).range = (actualConnectingHom P L n).ker := by
  ext y
  change (∃ x, KMap P L (n + 1) x = y) ↔
    connectingHom P n ((targetKEquiv P L (n + 1)).symm y) = 1
  change (∃ x, KMap P L (n + 1) x = y) ↔
    (targetKEquiv P L (n + 1)).symm y ∈ (connectingHom P n).ker
  rw [← quotient_range_eq_connecting_ker]
  change (∃ x, KMap P L (n + 1) x = y) ↔
    ∃ x, quotientKMap P (n + 1) x = (targetKEquiv P L (n + 1)).symm y
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, (targetKEquiv P L (n + 1)).injective ?_⟩
    simpa using hx
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    simpa using congrArg (targetKEquiv P L (n + 1)) hx

/-- The boundary's image is unchanged by transport along an equivalence. -/
theorem actualConnectingHom_range (n : ℕ) :
    (actualConnectingHom P L n).range = (connectingHom P n).range := by
  ext x
  change (∃ y, connectingHom P n ((targetKEquiv P L (n + 1)).symm y) = x) ↔
    ∃ y, connectingHom P n y = x
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨_, hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨targetKEquiv P L (n + 1) y, by simpa using hy⟩

/-- Exactness at the Serre-subcategory K-group in every nonnegative degree. -/
theorem actual_connecting_range_eq_inclusion_ker (n : ℕ) :
    (actualConnectingHom P L n).range = (Abelian.Devissage.KMap P n).ker := by
  rw [actualConnectingHom_range, connecting_range_eq_inclusion_ker]

/-- The original localization functor is surjective on genuine K₀. -/
theorem actualKZero_surjective : Function.Surjective (KMap P L 0) := by
  intro y
  obtain ⟨x, hx⟩ := quotientKZero_surjective P ((targetKEquiv P L 0).symm y)
  refine ⟨x, ?_⟩
  simpa using congrArg (targetKEquiv P L 0) hx

/-- The full connective localization sequence for the actual target and the
original functor, including its K₀ endpoint. No K-equivalence is a hypothesis. -/
theorem actual_localization_longExact :
    (∀ n, (Abelian.Devissage.KMap P n).range = (KMap P L n).ker) ∧
    (∀ n, (KMap P L (n + 1)).range = (actualConnectingHom P L n).ker) ∧
    (∀ n, (actualConnectingHom P L n).range = (Abelian.Devissage.KMap P n).ker) ∧
    Function.Surjective (KMap P L 0) :=
  ⟨actual_inclusion_range_eq_KMap_ker P L,
    actual_KMap_range_eq_connecting_ker P L,
    actual_connecting_range_eq_inclusion_ker P L, actualKZero_surjective P L⟩

/-- The low-degree tail for an actual Serre localization target. -/
theorem actual_localization_KZero_tail :
    (KMap P L 1).range = (actualConnectingHom P L 0).ker ∧
    (actualConnectingHom P L 0).range = (Abelian.Devissage.KMap P 0).ker ∧
    (Abelian.Devissage.KMap P 0).range = (KMap P L 0).ker ∧
    Function.Surjective (KMap P L 0) :=
  ⟨actual_KMap_range_eq_connecting_ker P L 0,
    actual_connecting_range_eq_inclusion_ker P L 0,
    actual_inclusion_range_eq_KMap_ker P L 0, actualKZero_surjective P L⟩

end CategoryTheory.ExactCategory.SerreLocalization

attribute [colib_ref "WeibelKBook" "V, Theorem 5.1, page 35" "adaptation"
  "Constructed transport of canonical Serre localization to an actual additive localization target"]
  CategoryTheory.ExactCategory.SerreLocalization.targetKEquiv
  CategoryTheory.ExactCategory.SerreLocalization.actualConnectingHom
  CategoryTheory.ExactCategory.SerreLocalization.actual_localization_longExact
  CategoryTheory.ExactCategory.SerreLocalization.actual_localization_KZero_tail

attribute [colib_tag "COL-0272",
  colib_ref "WeibelKBook" "V, Theorem 5.1, page 35" "adaptation"
    "Actual-target transport of canonical connective Serre localization"]
  CategoryTheory.ExactCategory.SerreLocalization.targetKEquiv
  CategoryTheory.ExactCategory.SerreLocalization.targetKEquiv_comp_quotientKMap
  CategoryTheory.ExactCategory.SerreLocalization.actualConnectingHom
  CategoryTheory.ExactCategory.SerreLocalization.actual_localization_longExact
  CategoryTheory.ExactCategory.SerreLocalization.actual_localization_KZero_tail
