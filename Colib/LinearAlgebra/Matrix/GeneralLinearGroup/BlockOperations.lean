/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.LinearAlgebra.Matrix.GeneralLinearGroup.ElementaryReindex
public import Colib.LinearAlgebra.Matrix.GeneralLinearGroup.BlockWhitehead

/-!
Implementation provenance:
`Quillen/Aglib/LinearAlgebra/Matrix/GeneralLinearGroup/BlockOperations.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Finite matrix permutations and block operations

Actual permutation units conjugate simultaneous reindexing. Block swaps,
composition of reindexings and rectangular inverse-matrix involutions
retain the original finite coordinate sets over an arbitrary ring.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w x
namespace Matrix.GeneralLinearGroup
variable (R : Type u) [Ring R]

/-- The actual permutation matrix as a matrix unit over a possibly noncommutative ring. -/
def permutationUnit {I : Type v} [Fintype I] [DecidableEq I] (e : I ≃ I) :
    (Matrix I I R)ˣ where
  val := (1 : Matrix I I R).submatrix e.symm (Equiv.refl I)
  inv := (1 : Matrix I I R).submatrix e (Equiv.refl I)
  val_inv := by
    rw [Matrix.one_submatrix_mul _ (Equiv.refl I)]
    ext i j
    simp [Matrix.submatrix, Matrix.one_apply]
  inv_val := by
    rw [Matrix.one_submatrix_mul _ (Equiv.refl I)]
    ext i j
    simp [Matrix.submatrix, Matrix.one_apply]

/-- Reindexing both coordinates is conjugation by the original permutation matrix. -/
lemma reindex_eq_conjugate {I : Type v} [Fintype I] [DecidableEq I]
    (e : I ≃ I) (g : (Matrix I I R)ˣ) :
    Units.mapEquiv (Matrix.reindexRingEquiv R e).toMulEquiv g =
      permutationUnit R e * g * (permutationUnit R e)⁻¹ := by
  apply Units.ext
  change g.val.submatrix e.symm e.symm =
    ((1 : Matrix I I R).submatrix e.symm (Equiv.refl I) * g.val) *
      (1 : Matrix I I R).submatrix e (Equiv.refl I)
  rw [Matrix.one_submatrix_mul _ (Equiv.refl I), Matrix.mul_submatrix_one e]
  rfl

/-- Composing finite coordinate relabellings composes the actual matrix-unit maps. -/
lemma reindex_trans {I : Type v} {J : Type w} {K : Type x} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
    (e : I ≃ J) (f : J ≃ K) (g : (Matrix I I R)ˣ) :
    Units.mapEquiv (Matrix.reindexRingEquiv R f).toMulEquiv
        (Units.mapEquiv (Matrix.reindexRingEquiv R e).toMulEquiv g) =
      Units.mapEquiv (Matrix.reindexRingEquiv R (e.trans f)).toMulEquiv g := by
  apply Units.ext
  rfl

/-- Interchanging the two finite blocks is the explicit sum-coordinate relabelling. -/
lemma reindex_blockSum_swap {I J : Type v} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (g : (Matrix I I R)ˣ) (h : (Matrix J J R)ˣ) :
    Units.mapEquiv (Matrix.reindexRingEquiv R (Equiv.sumComm I J)).toMulEquiv
        (Matrix.GeneralLinearGroup.blockSum g h) =
      Matrix.GeneralLinearGroup.blockSum h g := by
  apply Units.ext
  ext i j
  cases i <;> cases j <;> rfl

/-- Rectangular inverse matrices give an actual involution after taking their labelled sum. -/
def rectangularSwap {n m : ℕ} (a : Matrix (Fin n) (Fin m) R)
    (b : Matrix (Fin m) (Fin n) R) (hab : a * b = 1) (hba : b * a = 1) :
    (Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) R)ˣ where
  val := Matrix.fromBlocks 0 a b 0
  inv := Matrix.fromBlocks 0 a b 0
  val_inv := by simp [Matrix.fromBlocks_multiply, hab, hba]
  inv_val := by simp [Matrix.fromBlocks_multiply, hab, hba]

end Matrix.GeneralLinearGroup
