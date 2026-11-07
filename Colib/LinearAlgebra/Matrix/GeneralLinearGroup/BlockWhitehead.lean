/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary
public import Mathlib.Data.Matrix.Block

/-!
# Whitehead's block matrix factorization

Over any ring, upper and lower block unipotents are products of elementary
matrices. Consequently the block diagonal matrix with entries `g` and `g⁻¹`
is elementary. This is the finite matrix input to the stable Whitehead lemma;
it does not assert normality of the elementary subgroup at fixed rank.

The factorization is the identity in Weibel, *The K-book*, I, Exercise 1.11.

Implementation provenance: `Quillen/Aglib/LinearAlgebra/Matrix/BlockWhitehead.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. All matrices are native units.
-/
@[expose] public section

universe u v w

namespace Matrix.GeneralLinearGroup

open scoped commutatorElement

variable {R : Type u} [Ring R] {n : Type v} {m : Type w}
  [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The block sum of two invertible matrices. -/
def blockSum (g : (Matrix n n R)ˣ) (h : (Matrix m m R)ˣ) :
    (Matrix (n ⊕ m) (n ⊕ m) R)ˣ where
  val := Matrix.fromBlocks g.val 0 0 h.val
  inv := Matrix.fromBlocks g.inv 0 0 h.inv
  val_inv := by simp [Matrix.fromBlocks_multiply]
  inv_val := by simp [Matrix.fromBlocks_multiply]

lemma blockSum_mul (g g' : (Matrix n n R)ˣ) (h h' : (Matrix m m R)ˣ) :
    blockSum (g * g') (h * h') = blockSum g h * blockSum g' h' := by
  apply Units.ext
  simp [blockSum, Matrix.fromBlocks_multiply]

@[simp] lemma blockSum_one :
    blockSum (1 : (Matrix n n R)ˣ) (1 : (Matrix m m R)ˣ) = 1 := by
  apply Units.ext
  exact Matrix.fromBlocks_one

@[simp] lemma blockSum_elementary_one (i j : n) (hij : i ≠ j) (a : R) :
    blockSum (elementary i j hij a) (1 : (Matrix m m R)ˣ) =
      elementary (Sum.inl i) (Sum.inl j) (by simpa using hij) a := by
  apply Units.ext
  ext x y
  cases x <;> cases y <;>
    simp [blockSum, elementary, Matrix.single_apply, Matrix.one_apply]

/-- An upper block unipotent with an arbitrary rectangular off-diagonal block. -/
def upper (A : Matrix n m R) : (Matrix (n ⊕ m) (n ⊕ m) R)ˣ where
  val := Matrix.fromBlocks 1 A 0 1
  inv := Matrix.fromBlocks 1 (-A) 0 1
  val_inv := by simp [Matrix.fromBlocks_multiply]
  inv_val := by simp [Matrix.fromBlocks_multiply]

/-- A lower block unipotent with an arbitrary rectangular off-diagonal block. -/
def lower (A : Matrix m n R) : (Matrix (n ⊕ m) (n ⊕ m) R)ˣ where
  val := Matrix.fromBlocks 1 0 A 1
  inv := Matrix.fromBlocks 1 0 (-A) 1
  val_inv := by simp [Matrix.fromBlocks_multiply]
  inv_val := by simp [Matrix.fromBlocks_multiply]

@[simp] lemma upper_zero : upper (0 : Matrix n m R) = 1 := by
  apply Units.ext
  exact Matrix.fromBlocks_one

@[simp] lemma lower_zero : lower (0 : Matrix m n R) = 1 := by
  apply Units.ext
  exact Matrix.fromBlocks_one

lemma upper_add (A B : Matrix n m R) : upper (A + B) = upper A * upper B := by
  apply Units.ext
  simp [upper, Matrix.fromBlocks_multiply, add_comm]

lemma lower_add (A B : Matrix m n R) : lower (A + B) = lower A * lower B := by
  apply Units.ext
  simp [lower, Matrix.fromBlocks_multiply]

@[simp] lemma upper_single (i : n) (j : m) (a : R) :
    upper (Matrix.single i j a) = elementary (Sum.inl i) (Sum.inr j) (by simp) a := by
  apply Units.ext
  ext x y
  cases x <;> cases y <;> simp [upper, elementary, Matrix.single_apply, Matrix.one_apply]

@[simp] lemma lower_single (i : m) (j : n) (a : R) :
    lower (Matrix.single i j a) = elementary (Sum.inr i) (Sum.inl j) (by simp) a := by
  apply Units.ext
  ext x y
  cases x <;> cases y <;> simp [lower, elementary, Matrix.single_apply, Matrix.one_apply]

/-- Every upper block unipotent is in the genuine elementary subgroup. -/
lemma upper_mem_subgroup (A : Matrix n m R) : upper A ∈ elementarySubgroup (n ⊕ m) R := by
  rw [Matrix.matrix_eq_sum_single A]
  apply Finset.sum_induction _ (fun B => upper B ∈ elementarySubgroup (n ⊕ m) R)
  · intro A B hA hB
    rw [upper_add]
    exact Subgroup.mul_mem _ hA hB
  · simp
  · intro i _
    apply Finset.sum_induction _ (fun B => upper B ∈ elementarySubgroup (n ⊕ m) R)
    · intro A B hA hB
      rw [upper_add]
      exact Subgroup.mul_mem _ hA hB
    · simp
    · intro j _
      rw [upper_single]
      exact elementary_mem_subgroup _ _ _ _

/-- Every lower block unipotent is in the genuine elementary subgroup. -/
lemma lower_mem_subgroup (A : Matrix m n R) : lower A ∈ elementarySubgroup (n ⊕ m) R := by
  rw [Matrix.matrix_eq_sum_single A]
  apply Finset.sum_induction _ (fun B => lower B ∈ elementarySubgroup (n ⊕ m) R)
  · intro A B hA hB
    rw [lower_add]
    exact Subgroup.mul_mem _ hA hB
  · simp
  · intro i _
    apply Finset.sum_induction _ (fun B => lower B ∈ elementarySubgroup (n ⊕ m) R)
    · intro A B hA hB
      rw [lower_add]
      exact Subgroup.mul_mem _ hA hB
    · simp
    · intro j _
      rw [lower_single]
      exact elementary_mem_subgroup _ _ _ _

/-- Whitehead's explicit factorization, valid without commuting coefficients. -/
lemma blockSum_inv_factorization (g : (Matrix n n R)ˣ) :
    blockSum g g⁻¹ = upper g.val * lower (-g.inv) * upper g.val *
      (upper (-1 : Matrix n n R) * lower (1 : Matrix n n R) * upper (-1 : Matrix n n R)) := by
  apply Units.ext
  simp [blockSum, upper, lower, Matrix.fromBlocks_multiply]

/-- The original diagonal pair is a product of elementary matrices. -/
theorem blockSum_inv_mem_subgroup (g : (Matrix n n R)ˣ) :
    blockSum g g⁻¹ ∈ elementarySubgroup (n ⊕ n) R := by
  rw [blockSum_inv_factorization]
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ (upper_mem_subgroup _) (lower_mem_subgroup _))
      (upper_mem_subgroup _))
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ (upper_mem_subgroup _) (lower_mem_subgroup _))
      (upper_mem_subgroup _))

/-- A stabilized commutator factors through three elementary diagonal pairs. -/
lemma blockSum_commutator_factorization (g h : (Matrix n n R)ˣ) :
    blockSum ⁅g, h⁆ (1 : (Matrix n n R)ˣ) =
      blockSum g g⁻¹ * blockSum h h⁻¹ * blockSum (h * g)⁻¹ (h * g) := by
  rw [← blockSum_mul, ← blockSum_mul]
  congr 1
  · simp [commutatorElement_def, mul_assoc]
  · simp [mul_assoc]

/-- Every finite matrix commutator becomes elementary after doubling the rank. -/
theorem blockSum_commutator_mem_subgroup (g h : (Matrix n n R)ˣ) :
    blockSum ⁅g, h⁆ (1 : (Matrix n n R)ˣ) ∈ elementarySubgroup (n ⊕ n) R := by
  rw [blockSum_commutator_factorization]
  apply Subgroup.mul_mem _
    (Subgroup.mul_mem _ (blockSum_inv_mem_subgroup g) (blockSum_inv_mem_subgroup h))
  simpa only [inv_inv] using blockSum_inv_mem_subgroup (h * g)⁻¹

end Matrix.GeneralLinearGroup
