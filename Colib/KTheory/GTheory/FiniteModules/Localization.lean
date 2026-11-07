/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.FGModuleCat.Localization
public import Colib.Algebra.Module.LocalizedModule.FiniteTorsion
public import Colib.KTheory.GTheory.FiniteModules.FractionLocalization

/-!
# Connective G-localization at an arbitrary multiplicative set

The actual scalar-localization functor on finite modules over a commutative Noetherian
ring gives the connective G-localization sequence. Its supported objects are precisely
the finite modules annihilated by one element of the multiplicative set. For powers of
`r`, this means annihilation by one uniform power of `r`, including exponent zero.

The middle map is the original `ExactFunctor.smallKMap`. At the nonzerodivisors of a
domain it is definitionally the existing fraction-field map. No nontriviality or
exclusion of zero from the multiplicative set is required.

## Implementation provenance

Adapted from `Quillen/GTheory/FiniteModules/LocalizationSequence.lean` and
`Quillen/Aglib/Algebra/Category/FGModuleCat/SmallModelLocalization.lean` at Quillen
commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The categorical localization
is constructed on native `FGModuleCat` in the lower algebra layer, and the boundary
is the actual Serre localization boundary transported by its canonical equivalence.
-/
@[expose] public noncomputable section

universe u v

open CategoryTheory CategoryTheory.ExactCategory
open FGModuleCat.FractionLocalization (G)

attribute [local instance] Abelian.hasFiniteBiproducts

namespace FGModuleCat.Localization

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Small.{v, u} R]
  (S : Submonoid R)

/-- The actual kernel on Mathlib's chosen small model of finite modules. -/
abbrev supported : ObjectProperty (SmallModel.{u} (FGModuleCat.{v} R)) :=
  SmallModelGLocalization.supported (localizationExactFunctor S)

/-- Supported objects represent exactly the elementwise `S`-torsion modules. -/
theorem supported_iff (M : SmallModel.{u} (FGModuleCat.{v} R)) :
    supported S M ↔ localizationTorsionProperty S
      ((equivSmallModel (FGModuleCat.{v} R)).inverse.obj M) := by
  rw [supported, SmallModelGLocalization.supported, ExactFunctor.smallModel_kernel_iff]
  change (localizedModuleFunctor S).kernel _ ↔ _
  rw [localizedModuleFunctor_kernel]

/-- Finite generation turns elementwise torsion into one common annihilator. -/
theorem supported_iff_exists_annihilator (M : SmallModel.{u} (FGModuleCat.{v} R)) :
    supported S M ↔ ∃ s : S,
      ∀ x : (equivSmallModel (FGModuleCat.{v} R)).inverse.obj M, (s : R) • x = 0 := by
  rw [supported_iff]
  exact Module.Finite.forall_exists_smul_eq_zero_iff S

/-- Principal closed support is precisely annihilation by one uniform natural power. -/
theorem supported_powers_iff (r : R) (M : SmallModel.{u} (FGModuleCat.{v} R)) :
    supported (Submonoid.powers r) M ↔ ∃ n : ℕ,
      ∀ x : (equivSmallModel (FGModuleCat.{v} R)).inverse.obj M, r ^ n • x = 0 := by
  rw [supported_iff]
  exact Module.Finite.forall_exists_smul_eq_zero_powers_iff r

/-- The actual supported G-term, with its inherited abelian exact structure. -/
abbrev SupportedG (n : ℕ) :=
  SmallModelGLocalization.SupportedK (localizationExactFunctor.{u, v} S) n

/-- The original small-model map of the native scalar-localization functor. -/
def localizationKMap (n : ℕ) : G.{u, v} R n →* G.{u, v} (Localization S) n :=
  (localizationExactFunctor S).smallKMap n

/-- The actual supported inclusion on G-theory. -/
def supportedKMap (n : ℕ) : SupportedG.{u, v} S n →* G.{u, v} R n :=
  SmallModelGLocalization.inclusionKMap (localizationExactFunctor S) n

/-- The canonical Serre localization boundary with the original path-space sign. -/
def connectingHom (n : ℕ) :
    G.{u, v} (Localization S) (n + 1) →* SupportedG.{u, v} S n :=
  SmallModelGLocalization.connectingHom (localizationExactFunctor S) n

/-- Exactness at the original G-group, including degree zero. -/
theorem supported_range_eq_localization_ker (n : ℕ) :
    (supportedKMap.{u, v} S n).range = (localizationKMap S n).ker :=
  SmallModelGLocalization.inclusion_range_eq_KMap_ker (localizationExactFunctor S) n

/-- Exactness at the G-group of the actual localized ring. -/
theorem localization_range_eq_connecting_ker (n : ℕ) :
    (localizationKMap.{u, v} S (n + 1)).range = (connectingHom S n).ker :=
  SmallModelGLocalization.KMap_range_eq_connecting_ker (localizationExactFunctor S) n

/-- Exactness at the supported G-group, including degree zero. -/
theorem connecting_range_eq_supported_ker (n : ℕ) :
    (connectingHom.{u, v} S n).range = (supportedKMap S n).ker :=
  SmallModelGLocalization.connecting_range_eq_inclusion_ker (localizationExactFunctor S) n

/-- The actual homotopical G₀ map is surjective. -/
theorem localizationKZero_surjective :
    Function.Surjective (localizationKMap.{u, v} S 0) :=
  SmallModelGLocalization.KZero_surjective (localizationExactFunctor S)

/-- The full connective localization sequence for any multiplicative set. -/
theorem localization_longExact :
    (∀ n, (supportedKMap.{u, v} S n).range = (localizationKMap S n).ker) ∧
    (∀ n, (localizationKMap S (n + 1)).range = (connectingHom S n).ker) ∧
    (∀ n, (connectingHom S n).range = (supportedKMap S n).ker) ∧
    Function.Surjective (localizationKMap S 0) :=
  ⟨supported_range_eq_localization_ker S, localization_range_eq_connecting_ker S,
    connecting_range_eq_supported_ker S, localizationKZero_surjective S⟩

/-- The nonzerodivisor specialization retains the original fraction-field map literally. -/
theorem localizationKMap_nonZeroDivisors [IsDomain R] (n : ℕ) :
    localizationKMap.{u, v} (nonZeroDivisors R) n =
      FractionLocalization.localizationKMap R n := rfl

end FGModuleCat.Localization

attribute [colib_tag "COL-0273",
  colib_ref "WeibelKBook" "V, Theorem 5.1, page 35" "specialization"
    "Finite-module localization at any multiplicative set with the original K-map"]
  FGModuleCat.Localization.supported_iff
  FGModuleCat.Localization.supported_iff_exists_annihilator
  FGModuleCat.Localization.supported_powers_iff
  FGModuleCat.Localization.supported_range_eq_localization_ker
  FGModuleCat.Localization.localization_range_eq_connecting_ker
  FGModuleCat.Localization.connecting_range_eq_supported_ker
  FGModuleCat.Localization.localizationKZero_surjective
  FGModuleCat.Localization.localization_longExact
  FGModuleCat.Localization.localizationKMap_nonZeroDivisors
