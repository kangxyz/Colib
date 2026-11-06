/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.MilnorK.Norm.FiniteReciprocity

/-! Source-only consumers. These examples have not been elaborated. -/

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

universe u v

attribute [local instance] Ideal.Quotient.field

variable {k : Type u} [Field k] {ι : Type v}

example (s : Finset ι) (d : ι → ℕ) (ψ : ∀ i, MonicIrreducibleOfDegree k (d i))
    (hinj : Set.InjOn (fun i => poly (ψ i)) (s : Set ι))
    (y : MilnorKRing (RatFunc k))
    (hsupport : ∀ (e : ℕ) (χ : MonicIrreducibleOfDegree k e),
      (∀ i ∈ s, poly χ ≠ poly (ψ i)) → monicIrreducibleResidue χ y = 0) :
    (∑ i ∈ s, simpleMilnorNorm (ψ i) (monicIrreducibleResidue (ψ i) y)) =
      -infinityResidueRing k y :=
  sum_simpleMilnorNorm_residue_eq_neg_infinityResidueRing s d ψ hinj y hsupport

example (y : MilnorKRing (RatFunc k))
    (hy : ∀ (d : ℕ) (ψ : MonicIrreducibleOfDegree k d),
      monicIrreducibleResidue ψ y = 0) : infinityResidueRing k y = 0 :=
  infinityResidueRing_eq_zero_of_all_finite_residues_eq_zero y hy

example {d : ℕ} (f : MonicIrreducibleOfDegree k d)
    (x : MilnorKRing (Polynomial k ⧸ Ideal.span {poly f}))
    (y : MilnorKRing (RatFunc k)) (hy : IsSingleResidueLift f x y) :
    simpleMilnorNorm f x = -infinityResidueRing k y := by
  classical
  have h := sum_simpleMilnorNorm_eq_neg_infinityResidueRing_of_residues
    ({()} : Finset Unit) (fun _ => d) (fun _ => f)
    (fun a _ b _ _ => Subsingleton.elim a b) (fun _ => x) y
    (fun _ _ => hy.1) (fun e q hq => hy.2 e q (hq () (by simp)))
  simpa using h

example (s : Finset ι) (d : ι → ℕ) (ψ : ∀ i, MonicIrreducibleOfDegree k (d i))
    (hinj : Set.InjOn (fun i => poly (ψ i)) (s : Set ι)) :
    (∑ i ∈ s, simpleMilnorNorm (ψ i) (monicIrreducibleResidue (ψ i) 0)) =
      -infinityResidueRing k 0 :=
  sum_simpleMilnorNorm_residue_eq_neg_infinityResidueRing s d ψ hinj 0
    (fun _ _ _ => map_zero _)

example (n : ℕ) (s : Finset ι) (d : ι → ℕ)
    (ψ : ∀ i, MonicIrreducibleOfDegree k (d i))
    (hinj : Set.InjOn (fun i => poly (ψ i)) (s : Set ι))
    (y : MilnorKTheory (RatFunc k) (n + 1))
    (hsupport : ∀ (e : ℕ) (χ : MonicIrreducibleOfDegree k e),
      (∀ i ∈ s, poly χ ≠ poly (ψ i)) →
        monicIrreducibleResidue χ (y : MilnorKRing (RatFunc k)) = 0) :
    (∑ i ∈ s, simpleMilnorNorm (ψ i)
      (monicIrreducibleResidue (ψ i) (y : MilnorKRing (RatFunc k)))) =
        -infinityResidueRing k (y : MilnorKRing (RatFunc k)) :=
  sum_simpleMilnorNorm_residue_eq_neg_infinityResidueRing s d ψ hinj y hsupport

-- The extension degree already occurs in the native norm. No extra degree weight is used.
example {d : ℕ} (φ : MonicIrreducibleOfDegree k d) :
    simpleMilnorNorm φ 1 = (d : ℤ) • (1 : MilnorKRing k) :=
  simpleMilnorNorm_one φ

-- Infinity has the opposite sign to the affine norm contribution.
example {d : ℕ} (φ : MonicIrreducibleOfDegree k d) :
    infinityResidueRing k (milnorKSymbol (RatFunc k) (polyUnit (ne_zero φ))) =
      (-(d : ℤ)) • (1 : MilnorKRing k) := by
  rw [infinityResidueRing_milnorKSymbol_monic (monic φ), natDegree_eq φ]

-- Degree preservation is native and needs no separability assumption.
example {d i : ℕ} (φ : MonicIrreducibleOfDegree k d)
    {α : MilnorKRing (Polynomial k ⧸ Ideal.span {poly φ})}
    (hα : α ∈ milnorKGrading (Polynomial k ⧸ Ideal.span {poly φ}) i) :
    simpleMilnorNorm φ α ∈ milnorKGrading k i :=
  simpleMilnorNorm_mem_milnorKGrading φ hα

-- The empty-support case exercises the sigma-index corollary itself.
example :
    (∑ p ∈ (∅ : Finset (Σ d : ℕ, MonicIrreducibleOfDegree k d)),
      simpleMilnorNorm p.2 (monicIrreducibleResidue p.2 (0 : MilnorKRing (RatFunc k)))) +
      infinityResidueRing k 0 = 0 := by
  exact sum_simpleMilnorNorm_residue_add_infinity_eq_zero 0 ∅ (by
    intro p _
    exact map_zero _)

-- The single-residue polynomial symbol has precisely one affine contribution.
example {d : ℕ} (φ : MonicIrreducibleOfDegree k d) :
    simpleMilnorNorm φ 1 +
      infinityResidueRing k (milnorKSymbol (RatFunc k) (polyUnit (ne_zero φ))) = 0 := by
  classical
  have hs : ∀ p ∉ ({⟨d, φ⟩} : Finset (Σ e : ℕ, MonicIrreducibleOfDegree k e)),
      monicIrreducibleResidue p.2
        (milnorKSymbol (RatFunc k) (polyUnit (ne_zero φ))) = 0 := by
    rintro ⟨e, ψ⟩ hp
    apply (isSingleResidueLift_one φ).2 e ψ
    intro h
    obtain rfl : e = d := by rw [← natDegree_eq ψ, h, natDegree_eq φ]
    obtain rfl := poly_injective h
    exact hp (Finset.mem_singleton_self _)
  have h := sum_simpleMilnorNorm_residue_add_infinity_eq_zero
    (milnorKSymbol (RatFunc k) (polyUnit (ne_zero φ))) {⟨d, φ⟩} hs
  simpa only [Finset.sum_singleton, (isSingleResidueLift_one φ).1] using h

-- Reversing the position of a degree-one constant introduces the residue involution sign.
example {d : ℕ} (φ : MonicIrreducibleOfDegree k d) (a : kˣ) :
    monicIrreducibleResidue φ
      (milnorKSymbol (RatFunc k) (polyUnit (ne_zero φ)) *
        milnorKRingMap (constantsHom k) (milnorKSymbol k a)) =
      -milnorKRingMap (algebraMap k (Polynomial k ⧸ Ideal.span {poly φ}))
        (milnorKSymbol k a) := by
  rw [monicIrreducibleResidue_mul_constants, (isSingleResidueLift_one φ).1,
    one_mul, milnorKInvolution_milnorKRingMap, milnorKInvolution_milnorKSymbol, map_neg]

-- The finite-support existence corollary applies to nonhomogeneous whole-ring classes.
example (x : MilnorKRing (RatFunc k)) :
    ∃ S : Finset (Σ d : ℕ, MonicIrreducibleOfDegree k d),
      (∀ p ∉ S, monicIrreducibleResidue p.2 x = 0) ∧
      (∑ p ∈ S, simpleMilnorNorm p.2 (monicIrreducibleResidue p.2 x)) +
        infinityResidueRing k x = 0 :=
  exists_finset_sum_simpleMilnorNorm_residue_add_infinity_eq_zero x

end
