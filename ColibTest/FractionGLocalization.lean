/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.GTheory.FiniteModules.FractionLocalization

/-! Regression tests for the native fraction-field G-localization sequence. -/

open CategoryTheory CategoryTheory.ExactCategory

attribute [local instance] Abelian.hasFiniteBiproducts

universe u v

noncomputable section

namespace FGModuleCat.FractionLocalization.Tests

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [Small.{v, u} R]

example : (fractionExactFunctor.{u, v} R).toFunctor =
    Stacks.Examples.fgFractionModuleFunctor R := rfl

example (n : ℕ) : localizationKMap.{u, v} R n =
    (fractionExactFunctor R).smallKMap n := rfl

example (M : SmallModel.{u} (FGModuleCat.{v} R)) : supported R M ↔
    ∀ x : (equivSmallModel (FGModuleCat.{v} R)).inverse.obj M,
      ∃ s : nonZeroDivisors R, (s : R) • x = 0 :=
  supported_iff R M

example : (supportedKMap.{u, v} R 0).range = (localizationKMap R 0).ker :=
  supported_range_eq_localization_ker R 0

example : (localizationKMap.{u, v} R 1).range = (connectingHom R 0).ker :=
  localization_range_eq_connecting_ker R 0

example : (connectingHom.{u, v} R 0).range = (supportedKMap R 0).ker :=
  connecting_range_eq_supported_ker R 0

example : Function.Surjective (localizationKMap.{u, v} R 0) :=
  localizationKZero_surjective R

-- Equal module and ring universes require no extra smallness hypothesis.
example (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] :
    Function.Surjective (localizationKMap.{u, u} A 0) :=
  localizationKZero_surjective A

end FGModuleCat.FractionLocalization.Tests
