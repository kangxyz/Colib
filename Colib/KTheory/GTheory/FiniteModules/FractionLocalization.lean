/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.FGModuleCat.FractionLocalization
public import Colib.KTheory.Quillen.Localization.SmallModel

/-!
# Connective G-localization from a Noetherian domain to its fraction field

This is the full connective localization sequence for the actual native
fraction-field functor on finite modules. Its supported term consists exactly of
small-model objects representing torsion modules. The middle homomorphism is the
original `ExactFunctor.smallKMap`, including degree zero.

## Implementation provenance

Adapted from `Quillen/GTheory/FiniteModules/LocalizationSequence.lean` at Quillen
commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Here the actual native Stacks
fraction-field localization, Tag 0B0L, supplies the categorical theorem. No
arbitrary multiplicative-set or principal-open localization is claimed.
-/
@[expose] public noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory

attribute [local instance] Abelian.hasFiniteBiproducts

namespace FGModuleCat.FractionLocalization

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [Small.{v, u} R]

/-- Finite-module G-theory in Mathlib's chosen small model. -/
abbrev G (A : Type u) [CommRing A] [IsNoetherianRing A] (n : ℕ) :=
  (abelianExactStructure (FGModuleCat.{v} A)).SmallK.{u} n

/-- The actual Serre kernel on the chosen native small model. -/
abbrev supported : ObjectProperty (SmallModel.{u} (FGModuleCat.{v} R)) :=
  SmallModelGLocalization.supported (fractionExactFunctor R)

/-- Supported objects represent precisely the finite torsion modules. -/
theorem supported_iff (M : SmallModel.{u} (FGModuleCat.{v} R)) :
    supported R M ↔
      Stacks.Examples.fgTorsionModuleProperty R
        ((equivSmallModel (FGModuleCat.{v} R)).inverse.obj M) := by
  rw [supported, SmallModelGLocalization.supported, ExactFunctor.smallModel_kernel_iff]
  change (Stacks.Examples.fgFractionModuleFunctor R).kernel _ ↔ _
  rw [fractionModuleFunctor_kernel]

/-- The genuine supported G-term. -/
abbrev SupportedG (n : ℕ) :=
  SmallModelGLocalization.SupportedK (fractionExactFunctor.{u, v} R) n

/-- The original canonical small-model map of native scalar localization. -/
def localizationKMap (n : ℕ) : G.{u, v} R n →* G.{u, v} (FractionRing R) n :=
  (fractionExactFunctor R).smallKMap n

/-- The supported inclusion, with the canonical exact-structure comparison. -/
def supportedKMap (n : ℕ) : SupportedG.{u, v} R n →* G.{u, v} R n :=
  SmallModelGLocalization.inclusionKMap (fractionExactFunctor R) n

/-- The actual Serre localization boundary, transported to the native target. -/
def connectingHom (n : ℕ) :
    G.{u, v} (FractionRing R) (n + 1) →* SupportedG.{u, v} R n :=
  SmallModelGLocalization.connectingHom (fractionExactFunctor R) n

/-- Exactness at the original G-group, including degree zero. -/
theorem supported_range_eq_localization_ker (n : ℕ) :
    (supportedKMap.{u, v} R n).range = (localizationKMap R n).ker :=
  SmallModelGLocalization.inclusion_range_eq_KMap_ker (fractionExactFunctor R) n

/-- Exactness at the fraction-field G-group. -/
theorem localization_range_eq_connecting_ker (n : ℕ) :
    (localizationKMap.{u, v} R (n + 1)).range = (connectingHom R n).ker :=
  SmallModelGLocalization.KMap_range_eq_connecting_ker (fractionExactFunctor R) n

/-- Exactness at the genuine torsion-supported G-group, including degree zero. -/
theorem connecting_range_eq_supported_ker (n : ℕ) :
    (connectingHom.{u, v} R n).range = (supportedKMap R n).ker :=
  SmallModelGLocalization.connecting_range_eq_inclusion_ker (fractionExactFunctor R) n

/-- The sequence ends in the original homotopical G₀ surjection. -/
theorem localizationKZero_surjective :
    Function.Surjective (localizationKMap.{u, v} R 0) :=
  SmallModelGLocalization.KZero_surjective (fractionExactFunctor R)

/-- The complete connective fraction-field G-localization sequence. -/
theorem localization_longExact :
    (∀ n, (supportedKMap.{u, v} R n).range = (localizationKMap R n).ker) ∧
    (∀ n, (localizationKMap R (n + 1)).range = (connectingHom R n).ker) ∧
    (∀ n, (connectingHom R n).range = (supportedKMap R n).ker) ∧
    Function.Surjective (localizationKMap R 0) :=
  ⟨supported_range_eq_localization_ker R, localization_range_eq_connecting_ker R,
    connecting_range_eq_supported_ker R, localizationKZero_surjective R⟩

end FGModuleCat.FractionLocalization

attribute [colib_tag "COL-0273",
  colib_ref "WeibelKBook" "V, Theorem 5.1, page 35" "specialization"
    "Native finite-module fraction-field localization with the original K-map"]
  FGModuleCat.FractionLocalization.supported_iff
  FGModuleCat.FractionLocalization.supported_range_eq_localization_ker
  FGModuleCat.FractionLocalization.localization_range_eq_connecting_ker
  FGModuleCat.FractionLocalization.connecting_range_eq_supported_ker
  FGModuleCat.FractionLocalization.localizationKZero_surjective
  FGModuleCat.FractionLocalization.localization_longExact
