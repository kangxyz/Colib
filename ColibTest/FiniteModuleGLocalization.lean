/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.GTheory.FiniteModules.Localization

/-! Regression tests for arbitrary-set and principal closed-support G-localization. -/

open CategoryTheory CategoryTheory.ExactCategory

attribute [local instance] Abelian.hasFiniteBiproducts

universe u v

noncomputable section

namespace FGModuleCat.Localization.Tests

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Small.{v, u} R]
  (S : Submonoid R)

example : (localizationExactFunctor.{u, v} S).toFunctor =
    localizedModuleFunctor S := rfl

example (n : ℕ) : localizationKMap.{u, v} S n =
    (localizationExactFunctor S).smallKMap n := rfl

example (M : SmallModel.{u} (FGModuleCat.{v} R)) : supported S M ↔
    ∀ x : (equivSmallModel (FGModuleCat.{v} R)).inverse.obj M,
      ∃ s : S, (s : R) • x = 0 := supported_iff S M

example (M : SmallModel.{u} (FGModuleCat.{v} R)) : supported S M ↔
    ∃ s : S, ∀ x : (equivSmallModel (FGModuleCat.{v} R)).inverse.obj M,
      (s : R) • x = 0 := supported_iff_exists_annihilator S M

example (r : R) (M : SmallModel.{u} (FGModuleCat.{v} R)) :
    supported (Submonoid.powers r) M ↔
      ∃ n : ℕ, ∀ x : (equivSmallModel (FGModuleCat.{v} R)).inverse.obj M,
        r ^ n • x = 0 := supported_powers_iff r M

example : (supportedKMap.{u, v} S 0).range = (localizationKMap S 0).ker :=
  supported_range_eq_localization_ker S 0

example : (localizationKMap.{u, v} S 1).range = (connectingHom S 0).ker :=
  localization_range_eq_connecting_ker S 0

example : (connectingHom.{u, v} S 0).range = (supportedKMap S 0).ker :=
  connecting_range_eq_supported_ker S 0

example : Function.Surjective (localizationKMap.{u, v} S 0) :=
  localizationKZero_surjective S

-- Zero denominators are permitted: localization at powers of zero still has the sequence.
example : Function.Surjective (localizationKMap.{u, v} (Submonoid.powers (0 : R)) 0) :=
  localizationKZero_surjective _

example [IsDomain R] (n : ℕ) :
    localizationKMap.{u, v} (nonZeroDivisors R) n =
      FractionLocalization.localizationKMap R n := rfl

-- At equal universes no additional smallness hypothesis is required.
example (A : Type u) [CommRing A] [IsNoetherianRing A] (T : Submonoid A) :
    Function.Surjective (localizationKMap.{u, u} T 0) := localizationKZero_surjective T

end FGModuleCat.Localization.Tests
