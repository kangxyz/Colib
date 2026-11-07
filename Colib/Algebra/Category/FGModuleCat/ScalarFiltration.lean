/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Abelian.Devissage.CentralEndomorphism
public import Mathlib.Algebra.Category.FGModuleCat.Basic

/-!
# Scalar realization of finite image filtrations

A fully faithful realization in finitely generated modules pulls multiplication
by a scalar back to a natural endomorphism. Its categorical powers are exactly
the represented scalar powers. An additive realization reflects annihilation,
so actual modulewise nilpotence supplies the finite image filtration.

## Implementation provenance

Adapted from lines 150–192 of
`Quillen/Aglib/CategoryTheory/ExactCategory/Filtration/CentralEndomorphism.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The representation is the native fully faithful functor to Mathlib's
`FGModuleCat`; the category, ring and module-carrier universes remain independent.
No module quotient, localization or K-theory model is introduced here.
-/
@[expose] public section

noncomputable section

universe v u vR uR

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.Devissage.CentralEndomorphism

variable {C : Type u} [Category.{v} C] [Abelian C]

variable {R : Type uR} [CommRing R]
variable (F : C ⥤ FGModuleCat.{vR} R) [F.Full] [F.Faithful]

/-- Scalar multiplication pulled back through a fully faithful representation. -/
def scalar (f : R) : 𝟭 C ⟶ 𝟭 C where
  app X := F.preimage (FGModuleCat.ofHom (LinearMap.lsmul R (F.obj X) f))
  naturality {X Y} a := by
    apply F.map_injective
    simp only [Functor.id_map, Functor.map_comp, Functor.map_preimage]
    ext m
    exact ((F.map a).hom.hom.map_smul f m).symm

omit [Abelian C] in
@[simp] lemma map_scalar (f : R) (X : C) :
    F.map ((scalar F f).app X) =
      FGModuleCat.ofHom (LinearMap.lsmul R (F.obj X) f) := F.map_preimage _

omit [Abelian C] in
lemma map_power_apply (f : R) (X : C) (n : ℕ) (m : F.obj X) :
    (F.map (power (scalar F f) X n)).hom.hom m = f ^ n • m := by
  induction n with
  | zero => simp [power]
  | succ n ih =>
    simp only [power_succ, Functor.map_comp, map_scalar]
    change (F.map (power (scalar F f) X n)).hom.hom (f • m) = f ^ (n + 1) • m
    rw [map_smul, ih, smul_smul, pow_succ']

variable [F.Additive]

lemma scalar_killed_iff (f : R) (X : C) :
    killed (scalar F f) X ↔ ∀ m : F.obj X, f • m = 0 := by
  change (scalar F f).app X = 0 ↔ _
  rw [← F.map_injective.eq_iff, map_scalar, F.map_zero]
  constructor
  · intro h m
    exact congrArg (fun a ↦ a.hom.hom m) h
  · intro h
    ext m
    exact h m

lemma scalar_power_eq_zero (f : R) (X : C) (n : ℕ)
    (h : ∀ m : F.obj X, f ^ n • m = 0) : power (scalar F f) X n = 0 := by
  apply F.map_injective
  rw [F.map_zero]
  ext m
  exact (map_power_apply F f X n m).trans (h m)

end CategoryTheory.Abelian.Devissage.CentralEndomorphism
