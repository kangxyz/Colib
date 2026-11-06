/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.SimpleNorm

/-!
# Finite reciprocity for the existing polynomial Milnor norms

The finite sum of the existing simple norms of all nonzero finite residues is the negative
residue at infinity. The proof subtracts a finite sum of native single-residue lifts. It uses
only native exactness, not field-norm tower independence or a new total-norm definition.

A supplied finite family may contain extra zero-residue points, but distinct indices in its
support must give distinct polynomials. Degrees may vary. The family index has its own universe.
The sigma-index and finite-support existence statements are corollaries of this same proof.
They use the literal sigma type, avoiding the higher `MilnorExactSequence` import.

Source-only draft. No Lean/Lake command has been run on this file.
-/

@[expose] public noncomputable section

open Polynomial

universe u v

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

variable {k : Type u} [Field k] {ι : Type v}

/-- The sum of native polynomial norms of a complete finite residue family equals the
negative infinity residue. No field norm, separability, or characteristic hypothesis is used. -/
theorem sum_simpleMilnorNorm_residue_eq_neg_infinityResidueRing
    (s : Finset ι) (d : ι → ℕ) (ψ : ∀ i, MonicIrreducibleOfDegree k (d i))
    (hinj : Set.InjOn (fun i => poly (ψ i)) (s : Set ι))
    (y : MilnorKRing (RatFunc k))
    (hsupport : ∀ (e : ℕ) (χ : MonicIrreducibleOfDegree k e),
      (∀ i ∈ s, poly χ ≠ poly (ψ i)) → monicIrreducibleResidue χ y = 0) :
    (∑ i ∈ s, simpleMilnorNorm (ψ i) (monicIrreducibleResidue (ψ i) y)) =
      -infinityResidueRing k y := by
  classical
  let z : ι → MilnorKRing (RatFunc k) := fun i =>
    (exists_isSingleResidueLift_ring' (ψ i) (monicIrreducibleResidue (ψ i) y)).choose
  have hz (i : ι) : IsSingleResidueLift (ψ i) (monicIrreducibleResidue (ψ i) y) (z i) :=
    (exists_isSingleResidueLift_ring' (ψ i) (monicIrreducibleResidue (ψ i) y)).choose_spec
  have hres (i : ι) (hi : i ∈ s) :
      monicIrreducibleResidue (ψ i) (∑ j ∈ s, z j) =
        monicIrreducibleResidue (ψ i) y := by
    rw [map_sum]
    refine (Finset.sum_eq_single i ?_ ?_).trans (hz i).1
    · intro j hj hji
      exact (hz j).2 _ (ψ i) (fun h => hji (hinj hj hi h.symm))
    · intro hnot
      exact (hnot hi).elim
  have hzero (e : ℕ) (χ : MonicIrreducibleOfDegree k (e + 1)) :
      monicIrreducibleResidue χ (y - ∑ i ∈ s, z i) = 0 := by
    by_cases h : ∃ i ∈ s, poly χ = poly (ψ i)
    · obtain ⟨i, hi, hpoly⟩ := h
      apply monicIrreducibleResidue_eq_zero_of_poly_eq hpoly.symm
      rw [map_sub, hres i hi, sub_self]
    · have hne : ∀ i ∈ s, poly χ ≠ poly (ψ i) :=
        fun i hi heq => h ⟨i, hi, heq⟩
      have hsum : (∑ i ∈ s, monicIrreducibleResidue χ (z i)) = 0 :=
        Finset.sum_eq_zero (fun i hi => (hz i).2 _ χ (hne i hi))
      rw [map_sub, hsupport _ χ hne, map_sum, hsum, sub_self]
  have hinfinity : infinityResidueRing k y = ∑ i ∈ s, infinityResidueRing k (z i) := by
    apply sub_eq_zero.mp
    rw [← map_sum, ← map_sub]
    exact infinityResidueRing_eq_zero_of_mem_milnorKPolyFiltration_zero
      (mem_milnorKPolyFiltration_zero_of_forall_monicIrreducibleResidue_eq_zero hzero)
  calc
    (∑ i ∈ s, simpleMilnorNorm (ψ i) (monicIrreducibleResidue (ψ i) y)) =
        ∑ i ∈ s, -infinityResidueRing k (z i) :=
      Finset.sum_congr rfl (fun i _ => simpleMilnorNorm_eq (hz i))
    _ = -(∑ i ∈ s, infinityResidueRing k (z i)) := by rw [Finset.sum_neg_distrib]
    _ = -infinityResidueRing k y := congrArg Neg.neg hinfinity.symm

/-- Finite reciprocity with prescribed, possibly nonhomogeneous residue classes. The classes
live in the actual polynomial quotients, without a direct-sum or total-norm model. -/
theorem sum_simpleMilnorNorm_eq_neg_infinityResidueRing_of_residues
    (s : Finset ι) (d : ι → ℕ) (ψ : ∀ i, MonicIrreducibleOfDegree k (d i))
    (hinj : Set.InjOn (fun i => poly (ψ i)) (s : Set ι))
    (α : ∀ i, MilnorKRing (Polynomial k ⧸ Ideal.span {poly (ψ i)}))
    (y : MilnorKRing (RatFunc k))
    (hresidue : ∀ i ∈ s, monicIrreducibleResidue (ψ i) y = α i)
    (hsupport : ∀ (e : ℕ) (χ : MonicIrreducibleOfDegree k e),
      (∀ i ∈ s, poly χ ≠ poly (ψ i)) → monicIrreducibleResidue χ y = 0) :
    (∑ i ∈ s, simpleMilnorNorm (ψ i) (α i)) = -infinityResidueRing k y := by
  calc
    (∑ i ∈ s, simpleMilnorNorm (ψ i) (α i)) =
        ∑ i ∈ s, simpleMilnorNorm (ψ i) (monicIrreducibleResidue (ψ i) y) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hresidue i hi]
    _ = -infinityResidueRing k y :=
      sum_simpleMilnorNorm_residue_eq_neg_infinityResidueRing s d ψ hinj y hsupport

/-- Vanishing of every finite residue forces the infinity residue to vanish. This is the
empty-support endpoint, with no choice of lift or any norm map involved. -/
theorem infinityResidueRing_eq_zero_of_all_finite_residues_eq_zero
    (y : MilnorKRing (RatFunc k))
    (hy : ∀ (d : ℕ) (ψ : MonicIrreducibleOfDegree k d),
      monicIrreducibleResidue ψ y = 0) : infinityResidueRing k y = 0 :=
  infinityResidueRing_eq_zero_of_mem_milnorKPolyFiltration_zero
    (mem_milnorKPolyFiltration_zero_of_forall_monicIrreducibleResidue_eq_zero
      (fun e ψ => hy (e + 1) ψ))

private theorem finiteReciprocity_point_ext
    {p q : Σ d : ℕ, MonicIrreducibleOfDegree k d}
    (h : poly p.2 = poly q.2) : p = q := by
  obtain ⟨d, p⟩ := p
  obtain ⟨e, q⟩ := q
  obtain rfl : d = e := by rw [← natDegree_eq p, h, natDegree_eq q]
  obtain rfl := poly_injective h
  rfl

/-- The sigma-index form of finite reciprocity. Each polynomial occurs at most once, so no
separate injectivity hypothesis is needed. The infinity term has coefficient `+1`. -/
theorem sum_simpleMilnorNorm_residue_add_infinity_eq_zero
    (x : MilnorKRing (RatFunc k))
    (S : Finset (Σ d : ℕ, MonicIrreducibleOfDegree k d))
    (hS : ∀ p ∉ S, monicIrreducibleResidue p.2 x = 0) :
    (∑ p ∈ S, simpleMilnorNorm p.2 (monicIrreducibleResidue p.2 x)) +
      infinityResidueRing k x = 0 := by
  classical
  have h := sum_simpleMilnorNorm_residue_eq_neg_infinityResidueRing
    S (fun p => p.1) (fun p => p.2)
    (fun _ _ _ _ hpq => finiteReciprocity_point_ext hpq) x (by
      intro e χ hχ
      apply hS ⟨e, χ⟩
      intro hp
      exact hχ ⟨e, χ⟩ hp rfl)
  rw [h, neg_add_cancel]

/-- Every whole-ring class admits a finite affine support satisfying reciprocity. The support
comes from the native finite-support theorem; the equality uses the single generic proof above. -/
theorem exists_finset_sum_simpleMilnorNorm_residue_add_infinity_eq_zero
    (x : MilnorKRing (RatFunc k)) :
    ∃ S : Finset (Σ d : ℕ, MonicIrreducibleOfDegree k d),
      (∀ p ∉ S, monicIrreducibleResidue p.2 x = 0) ∧
      (∑ p ∈ S, simpleMilnorNorm p.2 (monicIrreducibleResidue p.2 x)) +
        infinityResidueRing k x = 0 := by
  classical
  obtain ⟨S, hS⟩ := exists_finset_forall_monicIrreducibleResidue_eq_zero x
  let T : Set (Σ d : ℕ, MonicIrreducibleOfDegree k d) :=
    (fun p => poly p.2) ⁻¹' (S : Set (Polynomial k))
  have hT : T.Finite :=
    S.finite_toSet.preimage fun p _ q _ h => finiteReciprocity_point_ext h
  have hs : ∀ p ∉ hT.toFinset, monicIrreducibleResidue p.2 x = 0 := by
    intro p hp
    exact hS _ p.2 fun h => hp (hT.mem_toFinset.mpr h)
  exact ⟨hT.toFinset, hs,
    sum_simpleMilnorNorm_residue_add_infinity_eq_zero x hT.toFinset hs⟩

end Stacks.Chow

end
