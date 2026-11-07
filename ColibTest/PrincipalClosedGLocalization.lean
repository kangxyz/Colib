/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.GTheory.FiniteModules.PrincipalClosedLocalization

/-! Regression tests for actual quotient restriction and principal closed/open G-localization. -/

open CategoryTheory CategoryTheory.ExactCategory
open FGModuleCat.FractionLocalization (G)

attribute [local instance] Abelian.hasFiniteBiproducts

universe u v

noncomputable section

namespace FGModuleCat.Localization.Tests

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Small.{v, u} R] (r : R)

example : (closedRestrictionExact.{u, v} r).toFunctor = closedRestriction r := rfl

example (n : ℕ) : closedPushforwardKMap.{u, v} r n =
    (closedRestrictionExact r).smallKMap n := rfl

example (n : ℕ) : (closedSupportGEquiv.{u, v} r n).toMonoidHom =
    closedSupportedKMap r n := closedSupportGEquiv_coe r n

example (n : ℕ) :
    (supportedKMap (Submonoid.powers r) n).comp
      (closedSupportGEquiv.{u, v} r n).toMonoidHom =
        (closedRestrictionExact r).smallKMap n := closedSupportGEquiv_pushforward r n

example (n : ℕ) : closedConnectingHom.{u, v} r n =
    (closedSupportGEquiv r n).symm.toMonoidHom.comp
      (connectingHom (Submonoid.powers r) n) := rfl

example : (closedPushforwardKMap.{u, v} r 0).range =
    (localizationKMap (Submonoid.powers r) 0).ker :=
  closedPushforward_range_eq_localization_ker r 0

example : (localizationKMap.{u, v} (Submonoid.powers r) 1).range =
    (closedConnectingHom r 0).ker := localization_range_eq_closedConnecting_ker r 0

example : (closedConnectingHom.{u, v} r 0).range =
    (closedPushforwardKMap r 0).ker := closedConnecting_range_eq_pushforward_ker r 0

example : Function.Surjective (localizationKMap.{u, v} (Submonoid.powers r) 0) :=
  (principalClosedLocalization_longExact r).2.2.2

-- Zero and units require no additional premise or changed map.
example (n : ℕ) : Function.Bijective (closedSupportedKMap.{u, v} (0 : R) n) :=
  closedSupportedKMap_bijective _ n

example (n : ℕ) : Function.Bijective (closedSupportedKMap.{u, v} (1 : R) n) :=
  closedSupportedKMap_bijective _ n

-- The actual quotient category equivalence itself needs neither Noetherianity nor smallness.
example (A : Type u) [CommRing A] (a : A) :
    FGModuleCat.{v} (ClosedRing a) ≌ (killedBy a).FullSubcategory := closedEquivalence a

-- Equal universes make the native smallness hypothesis automatic.
example (A : Type u) [CommRing A] [IsNoetherianRing A] (a : A) (n : ℕ) :
    G.{u, u} (ClosedRing a) n ≃* SupportedG.{u, u} (Submonoid.powers a) n :=
  closedSupportGEquiv a n

end FGModuleCat.Localization.Tests
