/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.NormalPrimeTrace

/-!
Regression consumers of restriction of the actual chosen norm as a Galois trace.
No perfectness, arbitrary-presentation comparison, or tower formula is supplied.
-/

noncomputable section

open Module Stacks.Chow
open scoped BigOperators

universe u

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [Normal k L] [Algebra.IsSeparable k L]

example (hp : Nat.Prime (finrank k L)) (x : MilnorKRing L) :
    milnorKRingMap (algebraMap k L) (milnorKNormRing k L x) =
      ∑ σ : L →ₐ[k] L, milnorKRingMap σ.toRingHom x :=
  milnorKNormRing_map_eq_sum_algHom_of_normal_prime hp x

example (hp : Nat.Prime (finrank k L)) (x : MilnorKRing L) :
    milnorKRingMap (algebraMap k L) (milnorKNormRing k L x) =
      ∑ σ : Gal(L/k), milnorKRingMap σ.toRingHom x :=
  milnorKNormRing_map_eq_sum_gal_of_normal_prime hp x

example (hp : Nat.Prime (finrank k L)) (n : ℕ) (x : MilnorKTheory L n) :
    milnorKTheoryMap (algebraMap k L) n (milnorKNorm k L n x) =
      ∑ σ : Gal(L/k), milnorKTheoryMap σ.toRingHom n x :=
  milnorKNorm_map_eq_sum_gal_of_normal_prime hp n x

example (hp : Nat.Prime (finrank k L)) (x : MilnorKRing L)
    (hx : ∀ σ : Gal(L/k), milnorKRingMap σ.toRingHom x = x) :
    milnorKRingMap (algebraMap k L) (milnorKNormRing k L x) =
      Fintype.card Gal(L/k) • x := by
  classical
  rw [milnorKNormRing_map_eq_sum_gal_of_normal_prime hp x]
  simp only [hx, Finset.sum_const, Finset.card_univ]

end
