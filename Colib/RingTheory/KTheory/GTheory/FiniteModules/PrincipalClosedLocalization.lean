/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.GTheory.FiniteModules.PrincipalClosedFunctor

/-!
# Principal closed pushforward and G-theory dévissage

The comparison is induced by actual quotient-ring restriction of scalars.
The finite-module quotient equivalence is used only for modules killed by f;
its passage to all supported modules is the proved image-filtration dévissage.

Adapted from `Quillen/AlgebraicGeometry/Scheme/Coherent/Affine/ClosedDevissage.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. This is a native
finite-module theorem; it imports no scheme or coherent-sheaf model.
-/
@[expose] public noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory CategoryTheory.Abelian
open FGModuleCat.FractionLocalization (G)

attribute [local instance] Abelian.hasFiniteBiproducts
namespace FGModuleCat.Localization
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Small.{v, u} R] (f : R)

instance smallClosedToKilledExact_mapQ_isEquivalence :
    (smallClosedToKilledExact.{u, v} f).mapQ.IsEquivalence := by
  apply CategoryTheory.ExactCategory.ExactFunctor.mapQ_isEquivalence_of_equivalence
  · intro M N a ha
    rw [show (abelianExactStructure (FGModuleCat.{v} (ClosedRing f))).smallModel =
      abelianExactStructure (SmallModel.{u} (FGModuleCat.{v} (ClosedRing f))) from
      abelianExactStructure_smallModel _]
    rw [abelianExactStructure_inflation_iff]
    have : Mono ((smallClosedToKilled.{u, v} f).map a) :=
      (abelianExactStructure_inflation_iff _ _).1 ha
    exact Functor.mono_of_mono_map (smallClosedToKilled.{u, v} f) this
  · intro M N a ha
    rw [show (abelianExactStructure (FGModuleCat.{v} (ClosedRing f))).smallModel =
      abelianExactStructure (SmallModel.{u} (FGModuleCat.{v} (ClosedRing f))) from
      abelianExactStructure_smallModel _]
    rw [abelianExactStructure_deflation_iff]
    have : Epi ((smallClosedToKilled.{u, v} f).map a) :=
      (abelianExactStructure_deflation_iff _ _).1 ha
    exact Functor.epi_of_epi_map (smallClosedToKilled.{u, v} f) this

/-- G-theory of the principal closed subscheme is isomorphic to supported G-theory. -/
def closedSupportGEquiv (n : ℕ) :
    G.{u, v} (ClosedRing f) n ≃* SupportedG.{u, v} (Submonoid.powers f) n :=
  ((smallClosedToKilledExact.{u, v} f).KEquivOfMapQIsEquivalence n).trans
    (principalDevissageKEquiv.{u, v} f n)

/-- The canonical closed-to-supported map, induced by actual restriction of scalars. -/
def closedSupportedKMap (n : ℕ) :
    G.{u, v} (ClosedRing f) n →* SupportedG.{u, v} (Submonoid.powers f) n :=
  (smallClosedToSupportExact.{u, v} f).KMap n

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] theorem closedSupportGEquiv_coe (n : ℕ) :
    ↑(closedSupportGEquiv.{u, v} f n) = closedSupportedKMap.{u, v} f n := by
  rw [closedSupportedKMap, smallClosedToSupportExact,
    CategoryTheory.ExactCategory.ExactFunctor.KMap_comp]
  rfl

/-- The actual closed-to-supported K-map is bijective in every connective degree. -/
theorem closedSupportedKMap_bijective (n : ℕ) :
    Function.Bijective (closedSupportedKMap.{u, v} f n) := by
  rw [← closedSupportGEquiv_coe]
  exact (closedSupportGEquiv.{u, v} f n).bijective

/-- The actual pushforward from the principal closed subscheme. -/
def closedPushforwardKMap (n : ℕ) : G.{u, v} (ClosedRing f) n →* G.{u, v} R n :=
  (closedRestrictionExact.{u, v} f).smallKMap n

/-- The dévissage comparison commutes with the original canonical closed
pushforward, including the small-model and zero-object normalizations. -/
theorem closedSupportGEquiv_pushforward (n : ℕ) :
    (supportedKMap (Submonoid.powers f) n).comp (closedSupportGEquiv.{u, v} f n).toMonoidHom =
      closedPushforwardKMap.{u, v} f n := by
  have h : ((smallClosedToKilledExact.{u, v} f).comp (CategoryTheory.ObjectProperty.exactInclusion
    (principalKilled.{u, v} f))).comp
      (CategoryTheory.ObjectProperty.exactInclusion (supported (Submonoid.powers f))) =
    (closedRestrictionExact.{u, v} f).smallModel.comp
      (CategoryTheory.SmallModel.abelianExactComparison (FGModuleCat.{v} R)) := by rfl
  have hk := congrArg (fun F ↦ F.KMap n) h
  simp only [CategoryTheory.ExactCategory.ExactFunctor.KMap_comp] at hk
  ext x
  apply (SmallModelLocalization.standardKEquiv (FGModuleCat.{v} R) n).injective
  change SmallModelLocalization.standardKEquiv (FGModuleCat.{v} R) n
    ((SmallModelLocalization.standardKEquiv (FGModuleCat.{v} R) n).symm
      (Devissage.KMap (supported (Submonoid.powers f)) n
        (Devissage.KMap (principalKilled.{u, v} f) n
          ((smallClosedToKilledExact.{u, v} f).KMap n x)))) = _
  rw [MulEquiv.apply_symm_apply]
  exact DFunLike.congr_fun hk x

/-- The boundary with values in G-theory of the actual principal closed subscheme. -/
def closedConnectingHom (n : ℕ) :
    G.{u, v} (Localization (Submonoid.powers f)) (n + 1) →* G.{u, v} (ClosedRing f) n :=
  (closedSupportGEquiv.{u, v} f n).symm.toMonoidHom.comp (connectingHom (Submonoid.powers f) n)

/-- Exactness at G_n(R), with actual closed pushforward and actual open localization. -/
theorem closedPushforward_range_eq_localization_ker (n : ℕ) :
    (closedPushforwardKMap.{u, v} f n).range = (localizationKMap (Submonoid.powers f) n).ker := by
  rw [← closedSupportGEquiv_pushforward]
  rw [MonoidHom.range_comp]
  rw [MonoidHom.range_eq_top.mpr (closedSupportGEquiv.{u, v} f n).surjective,
    ← MonoidHom.range_eq_map]
  exact supported_range_eq_localization_ker _ n

/-- Exactness at G_(n+1)(R[f⁻¹]) for the closed-subscheme boundary. -/
theorem localization_range_eq_closedConnecting_ker (n : ℕ) :
    (localizationKMap (Submonoid.powers f) (n + 1)).range =
      (closedConnectingHom.{u, v} f n).ker := by
  rw [localization_range_eq_connecting_ker]
  ext x
  simp only [MonoidHom.mem_ker, closedConnectingHom, MonoidHom.comp_apply,
    MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
  constructor
  · intro h; rw [h, map_one]
  · intro h
    apply (closedSupportGEquiv.{u, v} f n).symm.injective
    simpa only [map_one] using h

/-- Exactness at G_n(R/(f)), obtained by the proved canonical dévissage isomorphism. -/
theorem closedConnecting_range_eq_pushforward_ker (n : ℕ) :
    (closedConnectingHom.{u, v} f n).range = (closedPushforwardKMap.{u, v} f n).ker := by
  ext x
  rw [MonoidHom.mem_range, MonoidHom.mem_ker]
  constructor
  · rintro ⟨y, rfl⟩
    have hy : connectingHom (Submonoid.powers f) n y ∈
        (supportedKMap (Submonoid.powers f) n).ker := by
      rw [← connecting_range_eq_supported_ker]
      exact ⟨y, rfl⟩
    have hx := DFunLike.congr_fun (closedSupportGEquiv_pushforward f n)
      (closedConnectingHom.{u, v} f n y)
    simp only [MonoidHom.comp_apply, closedConnectingHom, MulEquiv.toMonoidHom_eq_coe,
      MonoidHom.coe_ofClass, MulEquiv.apply_symm_apply] at hx
    exact hx.symm.trans hy
  · intro hx
    have he : closedSupportGEquiv.{u, v} f n x ∈ (supportedKMap (Submonoid.powers f) n).ker := by
      change supportedKMap (Submonoid.powers f) n (closedSupportGEquiv.{u, v} f n x) = 1
      exact (DFunLike.congr_fun (closedSupportGEquiv_pushforward f n) x).trans hx
    rw [← connecting_range_eq_supported_ker] at he
    obtain ⟨y, hy⟩ := he
    refine ⟨y, ?_⟩
    change (closedSupportGEquiv.{u, v} f n).symm (connectingHom (Submonoid.powers f) n y) = x
    rw [hy, MulEquiv.symm_apply_apply]

/-- The genuine principal closed/open connective G-localization sequence,
including its terminal G₀ surjection. -/
theorem principalClosedLocalization_longExact :
    (∀ n, (closedPushforwardKMap.{u, v} f n).range =
      (localizationKMap (Submonoid.powers f) n).ker) ∧
    (∀ n, (localizationKMap (Submonoid.powers f) (n + 1)).range =
      (closedConnectingHom.{u, v} f n).ker) ∧
    (∀ n, (closedConnectingHom.{u, v} f n).range = (closedPushforwardKMap.{u, v} f n).ker) ∧
    Function.Surjective (localizationKMap (Submonoid.powers f) 0) :=
  ⟨closedPushforward_range_eq_localization_ker f, localization_range_eq_closedConnecting_ker f,
    closedConnecting_range_eq_pushforward_ker f, localizationKZero_surjective _⟩

end FGModuleCat.Localization

attribute [colib_tag "COL-0274",
  colib_ref "WeibelKBook" "V, Devissage Theorem 4.1 and proof, page 33" "specialization"
    "Quotient restriction and finite image filtrations identify principal supported G-theory",
  colib_ref "WeibelKBook" "V, Theorem 5.1, page 35" "specialization"
    "Principal closed/open localization with the original closed pushforward and open K-map"]
  FGModuleCat.Localization.closedSupportGEquiv
  FGModuleCat.Localization.closedSupportGEquiv_coe
  FGModuleCat.Localization.closedSupportedKMap_bijective
  FGModuleCat.Localization.closedSupportGEquiv_pushforward
  FGModuleCat.Localization.closedPushforward_range_eq_localization_ker
  FGModuleCat.Localization.localization_range_eq_closedConnecting_ker
  FGModuleCat.Localization.closedConnecting_range_eq_pushforward_ker
  FGModuleCat.Localization.principalClosedLocalization_longExact
