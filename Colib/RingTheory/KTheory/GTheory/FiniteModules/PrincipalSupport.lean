/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.FGModuleCat.ScalarFiltration
public import Colib.RingTheory.KTheory.GTheory.FiniteModules.Localization
public import Colib.KTheory.Quillen.Devissage.Theorem

/-!
# Finite image dévissage inside actual principal support

The supported category is the existing kernel on Mathlib's chosen small model.
Multiplication by the chosen ring element gives actual finite image filtrations
whose factors are killed by that element. This constructs, rather than assumes,
the input to the native homotopical dévissage theorem.

Adapted from `Quillen/Aglib/Algebra/Category/FGModuleCat/PrincipalSupportSmallModel.lean`
and `Quillen/Devissage/CentralEndomorphism.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory CategoryTheory.Abelian

attribute [local instance] Abelian.hasFiniteBiproducts

namespace FGModuleCat.Localization

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Small.{v, u} R] (r : R)

/-- The existing actual small abelian category supported on the powers of `r`. -/
abbrev PrincipalSupport := (supported.{u, v} (Submonoid.powers r)).FullSubcategory

/-- The fully faithful realization in the original finite modules. -/
abbrev principalRepresentation : PrincipalSupport.{u, v} r ⥤ FGModuleCat.{v} R :=
  (supported (Submonoid.powers r)).ι ⋙ (equivSmallModel (FGModuleCat.{v} R)).inverse

/-- Multiplication by `r`, transported through the actual fully faithful realization. -/
abbrev principalScalar : 𝟭 (PrincipalSupport.{u, v} r) ⟶ 𝟭 (PrincipalSupport r) :=
  Devissage.CentralEndomorphism.scalar (principalRepresentation r) r

/-- Supported modules killed by `r` itself, rather than merely a power of `r`. -/
abbrev principalKilled : ObjectProperty (PrincipalSupport.{u, v} r) :=
  Devissage.CentralEndomorphism.killed (principalScalar r)

/-- The categorical killed condition is ordinary scalar annihilation on the represented module. -/
theorem principalKilled_iff (M : PrincipalSupport.{u, v} r) :
    principalKilled r M ↔ ∀ m : (principalRepresentation r).obj M, r • m = 0 :=
  Devissage.CentralEndomorphism.scalar_killed_iff (principalRepresentation r) r M

/-- Actual finite image filtrations with factors annihilated by `r`. -/
theorem principalFiltrationHypothesis :
    Devissage.FiltrationHypothesis (principalKilled.{u, v} r) := by
  apply Devissage.CentralEndomorphism.filtrationHypothesis
  intro M
  obtain ⟨n, hn⟩ := (supported_powers_iff r M.obj).1 M.property
  exact ⟨n, Devissage.CentralEndomorphism.scalar_power_eq_zero
    (principalRepresentation r) r M n hn⟩

/-- The proved dévissage equivalence for the actual inclusion into principal support. -/
def principalDevissageKEquiv (n : ℕ) :
    (abelianExactStructure (principalKilled.{u, v} r).FullSubcategory).K n ≃*
      SupportedG.{u, v} (Submonoid.powers r) n :=
  Devissage.KEquiv (principalKilled r) (principalFiltrationHypothesis r) n

/-- Dévissage retains the canonical inclusion homomorphism. -/
@[simp]
theorem principalDevissageKEquiv_coe (n : ℕ) :
    ↑(principalDevissageKEquiv.{u, v} r n) =
      Devissage.KMap (principalKilled r) n := rfl

end FGModuleCat.Localization
