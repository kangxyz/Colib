/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.MilnorK.Norm.SplitBaseChange

/-! Uncompiled consumers of the actual separable split embedding-sum formula. -/

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

universe u

attribute [local instance] Ideal.Quotient.field

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

example {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    [Fintype ((k[X] ⧸ Ideal.span {poly p}) →ₐ[k] K)]
    (hsep : (poly p).Separable)
    (hsplit : ((poly p).map (algebraMap k K)).Splits)
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) :
    milnorKRingMap (algebraMap k K) (simpleMilnorNorm p x) =
      ∑ σ : (k[X] ⧸ Ideal.span {poly p}) →ₐ[k] K,
        milnorKRingMap σ.toRingHom x :=
  simpleMilnorNorm_map_eq_sum_algHom p hsep hsplit x

example {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    (hsep : (poly p).Separable)
    (hsplit : ((poly p).map (algebraMap k K)).Splits)
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) :
    letI : Fintype ((k[X] ⧸ Ideal.span {poly p}) →ₐ[k] K) :=
      PowerBasis.AlgHom.fintype (B := K) (AdjoinRoot.powerBasis' (monic p))
    milnorKRingMap (algebraMap k K) (simpleMilnorNorm p x) =
      ∑ σ : (k[X] ⧸ Ideal.span {poly p}) →ₐ[k] K,
        milnorKRingMap σ.toRingHom x :=
  simpleMilnorNorm_map_eq_sum_algHom_of_separable_of_splits p hsep hsplit x

example {d : ℕ} (p : MonicIrreducibleOfDegree k d)
    [Fintype ((k[X] ⧸ Ideal.span {poly p}) →ₐ[k] K)]
    (hsep : (poly p).Separable)
    (hsplit : ((poly p).map (algebraMap k K)).Splits) :
    (d : ℤ) • (1 : MilnorKRing K) =
      ∑ _σ : (k[X] ⧸ Ideal.span {poly p}) →ₐ[k] K, (1 : MilnorKRing K) := by
  simpa only [simpleMilnorNorm_one, map_zsmul, map_one] using
    simpleMilnorNorm_map_eq_sum_algHom p hsep hsplit 1

end
