/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.MilnorK.Norm.FiniteReciprocity
public import Mathlib.RingTheory.AdjoinRoot

/-!
# Single-lift reduction for polynomial scalar-factor norm comparison

These are conditional proof-reduction lemmas, not an unconditional scalar-base-change theorem.
They consume the exact finite-place residue equations, absence of other residues, and infinity
comparison for one native single-residue lift. Establishing those equations for the actual
coefficient map is a separate outstanding obligation, detailed in the source report.

The weighted reduction uses Mathlib's literal `AdjoinRoot.map` and the existing simple norms.
No norm, presentation wrapper, residue map, or rational-function map is defined here. Source
and target fields share the universe required by the pinned native `milnorKRingMap`.

Source-only draft. No Lean/Lake command has been run on this file.
-/

@[expose] public noncomputable section

open Polynomial

universe u v

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

variable {k K : Type u} [Field k] [Field K] {ι : Type v}

/-- A native single lift and its exact image-residue equations determine the image of its
simple norm. The comparison equations are hypotheses; this does not construct them. -/
theorem simpleMilnorNorm_map_eq_sum_of_lift_residues
    (φ : k →+* K) (Φ : RatFunc k →+* RatFunc K)
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
      ∑ i ∈ s, simpleMilnorNorm (q i) (α i) := by
  rw [simpleMilnorNorm_eq hy, map_neg, ← hinfinity]
  exact (sum_simpleMilnorNorm_eq_neg_infinityResidueRing_of_residues
    s e q hinj α (milnorKRingMap Φ y) hresidue hsupport).symm

/-- The same reduction with actual coefficient-factor maps and explicit nonnegative
multiplicities. Their numerical values and the residue equations are supplied, not inferred.
In particular this theorem must not be reported as an unconditional base-change formula. -/
theorem simpleMilnorNorm_map_eq_weighted_sum_of_lift_residues
    (φ : k →+* K) (Φ : RatFunc k →+* RatFunc K)
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
        (milnorKRingMap (AdjoinRoot.map φ (poly f) (poly (q i)) (hq i)) x) := by
  rw [simpleMilnorNorm_map_eq_sum_of_lift_residues φ Φ f x y hy s e q hinj
    (fun i => (m i : ℤ) •
      milnorKRingMap (AdjoinRoot.map φ (poly f) (poly (q i)) (hq i)) x)
    hresidue hsupport hinfinity]
  apply Finset.sum_congr rfl
  intro i _
  exact map_zsmul (simpleMilnorNorm (q i)) _ _

end Stacks.Chow

end
