/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.MilnorK.Norm.ScalarFactorReduction

/-! Source-only consumers of conditional reductions, not verified base-change examples. -/

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

universe u v

attribute [local instance] Ideal.Quotient.field

variable {k K : Type u} [Field k] [Field K] {ι : Type v}

example (φ : k →+* K) (Φ : RatFunc k →+* RatFunc K)
    {d : ℕ} (f : MonicIrreducibleOfDegree k d)
    (x : MilnorKRing (Polynomial k ⧸ Ideal.span {poly f}))
    (y : MilnorKRing (RatFunc k)) (hy : IsSingleResidueLift f x y)
    (s : Finset ι) (e : ι → ℕ) (q : ∀ i, MonicIrreducibleOfDegree K (e i))
    (hinj : Set.InjOn (fun i => poly (q i)) (s : Set ι))
    (α : ∀ i, MilnorKRing (Polynomial K ⧸ Ideal.span {poly (q i)}))
    (hresidue : ∀ i ∈ s,
      monicIrreducibleResidue (q i) (milnorKRingMap Φ y) = α i)
    (hsupport : ∀ (a : ℕ) (r : MonicIrreducibleOfDegree K a),
      (∀ i ∈ s, poly r ≠ poly (q i)) →
        monicIrreducibleResidue r (milnorKRingMap Φ y) = 0)
    (hinfinity : infinityResidueRing K (milnorKRingMap Φ y) =
      milnorKRingMap φ (infinityResidueRing k y)) :
    milnorKRingMap φ (simpleMilnorNorm f x) =
      ∑ i ∈ s, simpleMilnorNorm (q i) (α i) :=
  simpleMilnorNorm_map_eq_sum_of_lift_residues
    φ Φ f x y hy s e q hinj α hresidue hsupport hinfinity

example (φ : k →+* K) (Φ : RatFunc k →+* RatFunc K)
    {d : ℕ} (f : MonicIrreducibleOfDegree k d)
    (x : MilnorKRing (Polynomial k ⧸ Ideal.span {poly f}))
    (y : MilnorKRing (RatFunc k)) (hy : IsSingleResidueLift f x y)
    (s : Finset ι) (e : ι → ℕ) (q : ∀ i, MonicIrreducibleOfDegree K (e i))
    (hinj : Set.InjOn (fun i => poly (q i)) (s : Set ι))
    (hq : ∀ i, poly (q i) ∣ (poly f).map φ) (m : ι → ℕ)
    (hresidue : ∀ i ∈ s,
      monicIrreducibleResidue (q i) (milnorKRingMap Φ y) =
        (m i : ℤ) • milnorKRingMap (AdjoinRoot.map φ (poly f) (poly (q i)) (hq i)) x)
    (hsupport : ∀ (a : ℕ) (r : MonicIrreducibleOfDegree K a),
      (∀ i ∈ s, poly r ≠ poly (q i)) →
        monicIrreducibleResidue r (milnorKRingMap Φ y) = 0)
    (hinfinity : infinityResidueRing K (milnorKRingMap Φ y) =
      milnorKRingMap φ (infinityResidueRing k y)) :
    milnorKRingMap φ (simpleMilnorNorm f x) =
      ∑ i ∈ s, (m i : ℤ) • simpleMilnorNorm (q i)
        (milnorKRingMap (AdjoinRoot.map φ (poly f) (poly (q i)) (hq i)) x) :=
  simpleMilnorNorm_map_eq_weighted_sum_of_lift_residues
    φ Φ f x y hy s e q hinj hq m hresidue hsupport hinfinity

end
