/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! # Finite matrix stabilization and change of coefficients

The original finite matrix-unit groups, block stabilization, finite-rank
transition maps and entrywise ring maps are retained over arbitrary rings.
This file does not construct their stable direct-limit group.

## Implementation provenance

Adapted from `Quillen/Aglib/LinearAlgebra/Matrix/GeneralLinearGroup/Stabilization.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The finite groups are Mathlib's
`Matrix.GeneralLinearGroup`, including rank zero.
-/
@[expose] public section

universe u
namespace StableGeneralLinear
variable (R : Type u) [Ring R]

/-- Adjoin a one-dimensional identity block before reindexing. -/
def blockStep (n : ℕ) : Matrix.GeneralLinearGroup (Fin n) R →* (Matrix (Fin n ⊕ Fin 1) (Fin n ⊕
  Fin 1) R)ˣ where
  toFun g :=
    { val := Matrix.fromBlocks g.val 0 0 1
      inv := Matrix.fromBlocks g.inv 0 0 1
      val_inv := by simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
      inv_val := by simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_one] }
  map_one' := by apply Units.ext; exact Matrix.fromBlocks_one
  map_mul' g h := by
    apply Units.ext
    simp [Matrix.fromBlocks_multiply]

/-- The usual stabilization `g ↦ diag(g,1)` in the standard finite indexing. -/
def step (n : ℕ) : Matrix.GeneralLinearGroup (Fin n) R →* Matrix.GeneralLinearGroup (Fin (n +
  1)) R :=
  (Units.map (Matrix.reindexRingEquiv R finSumFinEquiv).toMonoidHom).comp (blockStep R n)

@[simp] lemma step_val_castSucc (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) (i j : Fin n) :
    (step R n g).val i.castSucc j.castSucc = g.val i j := by
  change Matrix.fromBlocks g.val 0 0 (1 : Matrix (Fin 1) (Fin 1) R)
    (finSumFinEquiv.symm i.castSucc) (finSumFinEquiv.symm j.castSucc) = _
  simp

@[simp] lemma step_val_last (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (step R n g).val (Fin.last n) (Fin.last n) = 1 := by
  change Matrix.fromBlocks g.val 0 0 (1 : Matrix (Fin 1) (Fin 1) R)
    (finSumFinEquiv.symm (Fin.last n)) (finSumFinEquiv.symm (Fin.last n)) = _
  simp

@[simp] lemma step_val_castSucc_last (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) (i : Fin n) :
    (step R n g).val i.castSucc (Fin.last n) = 0 := by
  change Matrix.fromBlocks g.val 0 0 (1 : Matrix (Fin 1) (Fin 1) R)
    (finSumFinEquiv.symm i.castSucc) (finSumFinEquiv.symm (Fin.last n)) = _
  simp

@[simp] lemma step_val_last_castSucc (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) (j : Fin n) :
    (step R n g).val (Fin.last n) j.castSucc = 0 := by
  change Matrix.fromBlocks g.val 0 0 (1 : Matrix (Fin 1) (Fin 1) R)
    (finSumFinEquiv.symm (Fin.last n)) (finSumFinEquiv.symm j.castSucc) = _
  simp

lemma step_injective (n : ℕ) : Function.Injective (step R n) := by
  intro g h e
  apply Units.ext
  have e' := congrArg (fun a : Matrix.GeneralLinearGroup (Fin (n + 1)) R =>
    a.val.submatrix (fun i => finSumFinEquiv (Sum.inl i))
      (fun i => finSumFinEquiv (Sum.inl i))) e
  ext i j
  have e'' := congrFun (congrFun e' i) j
  change Matrix.fromBlocks g.val 0 0 (1 : Matrix (Fin 1) (Fin 1) R)
      (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl i)))
      (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl j))) =
    Matrix.fromBlocks h.val 0 0 (1 : Matrix (Fin 1) (Fin 1) R)
      (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl i)))
      (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl j))) at e''
  simpa only [Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁] using e''


/-- The transition map from rank `n` to rank `m`. -/
def transition (n m : ℕ) (h : n ≤ m) : Matrix.GeneralLinearGroup (Fin n) R →*
  Matrix.GeneralLinearGroup (Fin m) R where
  toFun := Nat.leRecOn h (fun {k} => step R k)
  map_one' := by
    induction h using Nat.leRec with
    | refl => exact Nat.leRecOn_self _
    | @le_succ_of_le m h ih => rw [Nat.leRecOn_succ h, ih, map_one]
  map_mul' g k := by
    induction h using Nat.leRec with
    | refl => simp only [Nat.leRecOn_self]
    | @le_succ_of_le m h ih => simp only [Nat.leRecOn_succ h, ih, map_mul]

@[simp] lemma transition_self (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    transition R n n le_rfl g = g :=
  Nat.leRecOn_self (C := fun k => Matrix.GeneralLinearGroup (Fin k) R) g

lemma transition_trans {n m k : ℕ} (h : n ≤ m) (h' : m ≤ k)
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    transition R m k h' (transition R n m h g) = transition R n k (h.trans h') g :=
  (Nat.leRecOn_trans (C := fun k => Matrix.GeneralLinearGroup (Fin k) R) h h' g).symm

@[simp] lemma transition_succ (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    transition R n (n + 1) (Nat.le_succ n) g = step R n g :=
  Nat.leRecOn_succ' (C := fun k => Matrix.GeneralLinearGroup (Fin k) R) g

lemma transition_step {n m : ℕ} (h : n ≤ m) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    transition R n (m + 1) (Nat.le_succ_of_le h) g = step R m (transition R n m h g) :=
  Nat.leRecOn_succ (C := fun k => Matrix.GeneralLinearGroup (Fin k) R) h g

/-- Stabilization leaves all original matrix entries unchanged. -/
@[simp] lemma transition_val_castLE {n m : ℕ} (h : n ≤ m) (g : Matrix.GeneralLinearGroup (Fin n) R)
    (i j : Fin n) :
    (transition R n m h g).val (i.castLE h) (j.castLE h) = g.val i j := by
  induction h using Nat.leRec with
  | refl => simp
  | @le_succ_of_le m h ih =>
    rw [transition_step R h g]
    change (step R m (transition R n m h g)).val
      (i.castLE h).castSucc (j.castLE h).castSucc = _
    rw [step_val_castSucc, ih]

/-- Every row beyond the original rank is the corresponding identity row. -/
lemma transition_val_of_le_left {n m : ℕ} (h : n ≤ m) (g : Matrix.GeneralLinearGroup (Fin n) R)
    (i j : Fin m) (hi : n ≤ i.val) :
    (transition R n m h g).val i j = (1 : Matrix (Fin m) (Fin m) R) i j := by
  induction h using Nat.leRec with
  | refl => exact False.elim (Nat.not_le_of_gt i.isLt hi)
  | @le_succ_of_le m h ih =>
    rw [transition_step R h g]
    cases i using Fin.lastCases <;> cases j using Fin.lastCases <;>
      simp_all [Matrix.one_apply, eq_comm]

/-- Every column beyond the original rank is the corresponding identity column. -/
lemma transition_val_of_le_right {n m : ℕ} (h : n ≤ m) (g : Matrix.GeneralLinearGroup (Fin n) R)
    (i j : Fin m) (hj : n ≤ j.val) :
    (transition R n m h g).val i j = (1 : Matrix (Fin m) (Fin m) R) i j := by
  induction h using Nat.leRec with
  | refl => exact False.elim (Nat.not_le_of_gt j.isLt hj)
  | @le_succ_of_le m h ih =>
    rw [transition_step R h g]
    cases i using Fin.lastCases <;> cases j using Fin.lastCases <;>
      simp_all [Matrix.one_apply, eq_comm]

/-- Arbitrary stabilization is a block diagonal extension by an identity matrix. -/
lemma transition_val_fromBlocks (n m : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (transition R n (n + m) (Nat.le_add_right n m) g).val =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks g.val 0 0 (1 : Matrix (Fin m) (Fin m) R)) := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  cases i with
  | inl i =>
    cases j with
    | inl j => exact transition_val_castLE R _ g i j
    | inr j =>
      rw [transition_val_of_le_right R _ g _ _ (Nat.le_add_right n j.val)]
      simp only [Matrix.one_apply, Equiv.apply_eq_iff_eq]
      simp
  | inr i =>
    rw [transition_val_of_le_left R _ g _ _ (Nat.le_add_right n i.val)]
    cases j <;> simp only [Matrix.one_apply, Equiv.apply_eq_iff_eq] <;> simp [Matrix.one_apply]

instance : DirectedSystem ((fun n => Matrix.GeneralLinearGroup (Fin n) R)) (fun n m h =>
  transition R n m h) where
  map_self := fun {_} => transition_self R _
  map_map := fun {_ _ _} => transition_trans R

lemma transition_injective (n m : ℕ) (h : n ≤ m) :
    Function.Injective (transition R n m h) := by
  induction h using Nat.leRec with
  | refl => intro g k e; simpa using e
  | @le_succ_of_le m h ih =>
    intro g k e
    apply ih
    apply step_injective R m
    simpa only [transition, MonoidHom.coe_mk, OneHom.coe_mk, Nat.leRecOn_succ h] using e

section RingMap
variable {R} {S : Type*} [Ring S] {T : Type*} [Ring T]

/-- Entrywise change of rings at a finite stage, for arbitrary rings. -/
def finiteMap (f : R →+* S) (n : ℕ) : Matrix.GeneralLinearGroup (Fin n) R →*
  Matrix.GeneralLinearGroup (Fin n) S :=
  Units.map (RingHom.mapMatrix f).toMonoidHom

lemma finiteMap_step (f : R →+* S) (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    finiteMap f (n + 1) (step R n g) = step S n (finiteMap f n g) := by
  apply Units.ext
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  change f (Matrix.fromBlocks g.val 0 0 (1 : Matrix (Fin 1) (Fin 1) R)
      (finSumFinEquiv.symm (finSumFinEquiv i))
      (finSumFinEquiv.symm (finSumFinEquiv j))) =
    Matrix.fromBlocks (g.val.map f) 0 0 (1 : Matrix (Fin 1) (Fin 1) S)
      (finSumFinEquiv.symm (finSumFinEquiv i))
      (finSumFinEquiv.symm (finSumFinEquiv j))
  simp only [Equiv.symm_apply_apply]
  cases i <;> cases j <;> simp [Matrix.one_apply]

lemma finiteMap_transition (f : R →+* S) {n m : ℕ} (h : n ≤ m) (g : Matrix.GeneralLinearGroup
  (Fin n) R) :
    finiteMap f m (transition R n m h g) = transition S n m h (finiteMap f n g) := by
  induction h using Nat.leRec with
  | refl => simp
  | @le_succ_of_le m h ih =>
    change finiteMap f (m + 1) (Nat.leRecOn (C := (fun n => Matrix.GeneralLinearGroup (Fin n)
      R)) _ (fun {k} => step R k) g) =
      Nat.leRecOn (C := (fun n => Matrix.GeneralLinearGroup (Fin n) S)) _ (fun {k} => step S k)
        (finiteMap f n g)
    rw [Nat.leRecOn_succ h, Nat.leRecOn_succ h, finiteMap_step]
    exact congrArg (step S m) ih

end RingMap
end StableGeneralLinear
