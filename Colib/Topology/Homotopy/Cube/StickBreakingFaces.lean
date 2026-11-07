/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.Cube.StickBreaking
public import Colib.Analysis.Convex.StdSimplex.Skeleton

/-!
# The ordered faces of the stick-breaking quotient

Every lower cube face is the corresponding increasing simplex face, composed
with the same quotient one dimension down. Every upper cube face except the
last has two zero barycentric coordinates; the last is the final simplex face.
These are literal coordinate equations, not asserted orientation properties of
an arbitrary cube/simplex homeomorphism.
-/

/-! Implementation source: `Quillen/Topology/Cube/StickBreakingFaces.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Native function-subtype coordinates
and the actual ordered stick-breaking quotient are used throughout. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Topology
open scoped Topology unitInterval

namespace Cube

private theorem insertNth_mul {n : ℕ} (j : Fin (n + 1)) (c : ℝ) (f : Fin n → ℝ) :
    Fin.insertNth (α := fun _ ↦ ℝ) j 0 (fun k ↦ c * f k) =
      fun k ↦ c * Fin.insertNth (α := fun _ ↦ ℝ) j 0 f k := by
  ext k
  refine Fin.succAboveCases j ?_ (fun i ↦ ?_) k
  · simp
  · simp

/-- Inserting a zero cube coordinate inserts a zero barycentric coordinate in
exactly the same position, without permuting any other coordinates. -/
theorem stickWeights_insert_zero (n : ℕ) (j : Fin (n + 1)) (t : Fin n → I) :
    stickWeights (n + 1) (j.insertNth 0 t) =
      j.castSucc.insertNth 0 (stickWeights n t) := by
  induction n with
  | zero =>
    have hj : j = 0 := Fin.ext (by omega)
    subst j
    ext k
    refine Fin.cases ?_ (fun i ↦ ?_) k <;> simp [stickWeights, Fin.insertNth_zero']
  | succ n ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) j
    · ext k
      refine Fin.cases ?_ (fun i ↦ ?_) k <;> simp [stickWeights, Fin.insertNth_zero']
    · rw [← Fin.cons_self_tail t, Fin.insertNth_succ_cons]
      change Fin.cons (t 0 : ℝ)
          (fun k ↦ (1 - (t 0 : ℝ)) * stickWeights (n + 1)
            (j.insertNth 0 (Fin.tail t)) k) =
        Fin.insertNth (α := fun _ ↦ ℝ) j.castSucc.succ 0
          (Fin.cons (t 0 : ℝ) (fun k ↦ (1 - (t 0 : ℝ)) * stickWeights n (Fin.tail t) k))
      rw [Fin.insertNth_succ_cons, ih, insertNth_mul]

private theorem map_succAbove_weights {n : ℕ} (x : _root_.stdSimplex ℝ (Fin (n + 1)))
    (j : Fin (n + 2)) (k : Fin (n + 2)) :
    stdSimplex.map j.succAbove x k = Fin.insertNth (α := fun _ ↦ ℝ) j 0 (fun i ↦ x i) k := by
  refine Fin.succAboveCases j ?_ (fun i ↦ ?_) k
  · rw [Fin.insertNth_apply_same]
    exact stdSimplex.map_apply_eq_zero_of_not_mem_range j.succAbove x j
      (by simp [Fin.range_succAbove])
  · simp only [Fin.insertNth_apply_succAbove,
      stdSimplex.map_apply_of_injective j.succAbove Fin.succAbove_right_injective]

/-- The exact lower-face equation with increasing simplex-face order. -/
theorem stickBreaking_lower_face (n : ℕ) (j : Fin (n + 1)) (t : Fin n → I) :
    stickBreaking (n + 1) (j.insertNth 0 t) =
      stdSimplex.map j.castSucc.succAbove (stickBreaking n t) := by
  apply stdSimplex.ext
  ext k
  rw [map_succAbove_weights]
  exact congrFun (stickWeights_insert_zero n j t) k

/-- Setting one cube coordinate to one annihilates all later barycentric coordinates. -/
theorem stickWeights_upper_eq_zero (n : ℕ) (j : Fin (n + 1)) (t : Fin n → I)
    (k : Fin (n + 2)) (hjk : (j : ℕ) < k) :
    stickWeights (n + 1) (j.insertNth 1 t) k = 0 := by
  induction n with
  | zero =>
    have hj : j = 0 := Fin.ext (by omega)
    subst j
    cases k using Fin.cases with
    | zero => simp at hjk
    | succ i => simp [stickWeights]
  | succ n ih =>
    cases j using Fin.cases with
    | zero =>
      cases k using Fin.cases with
      | zero => simp at hjk
      | succ i => simp [stickWeights, Fin.insertNth_zero']
    | succ j =>
      rw [← Fin.cons_self_tail t, Fin.insertNth_succ_cons]
      cases k using Fin.cases with
      | zero => simp at hjk
      | succ i =>
        simp only [stickWeights_succ_succ, Fin.cons_zero, Fin.tail_cons]
        rw [ih j (Fin.tail t) i (by exact Nat.lt_of_succ_lt_succ hjk), mul_zero]

/-- Every non-final upper face lands in the genuine codimension-two skeleton. -/
theorem stickBreaking_upper_two_zero {n : ℕ} (j : Fin (n + 1))
    (hj : (j : ℕ) < n) (t : Fin n → I) :
    ∃ i k : Fin (n + 2), i ≠ k ∧
      (stickBreaking (n + 1) (j.insertNth 1 t)) i = 0 ∧
      (stickBreaking (n + 1) (j.insertNth 1 t)) k = 0 := by
  let i : Fin (n + 2) := ⟨j.val + 1, by omega⟩
  let k : Fin (n + 2) := ⟨j.val + 2, by omega⟩
  refine ⟨i, k, ?_, ?_, ?_⟩
  · intro h
    have hval : j.val + 1 = j.val + 2 := congrArg Fin.val h
    omega
  · exact stickWeights_upper_eq_zero n j t i (by change j.val < j.val + 1; omega)
  · exact stickWeights_upper_eq_zero n j t k (by change j.val < j.val + 2; omega)

private theorem snoc_mul {n : ℕ} (c : ℝ) (f : Fin n → ℝ) :
    Fin.snoc (α := fun _ ↦ ℝ) (fun k ↦ c * f k) 0 =
      fun k ↦ c * Fin.snoc (α := fun _ ↦ ℝ) f 0 k := by
  ext k
  refine Fin.lastCases ?_ (fun i ↦ ?_) k <;> simp

/-- On the final upper cube face the final barycentric coordinate is zero,
while every preceding coordinate retains its increasing order. -/
theorem stickWeights_snoc_one (n : ℕ) (t : Fin n → I) :
    stickWeights (n + 1) (Fin.snoc t 1) = Fin.snoc (stickWeights n t) 0 := by
  induction n with
  | zero =>
    ext k
    refine Fin.cases ?_ (fun i ↦ ?_) k
    · simp [stickWeights, Fin.snoc_zero]
    · have hi : i = 0 := Fin.ext (by omega)
      subst i
      have hs : Fin.snoc (α := fun _ ↦ ℝ) (fun _ : Fin 1 ↦ 1) 0 (1 : Fin 2) = 0 :=
        Fin.snoc_last _ _
      simp [stickWeights, Fin.snoc_zero, hs]
  | succ n ih =>
    rw [← Fin.cons_self_tail t, ← Fin.cons_snoc_eq_snoc_cons]
    change Fin.cons (t 0 : ℝ)
        (fun k ↦ (1 - (t 0 : ℝ)) * stickWeights (n + 1) (Fin.snoc (Fin.tail t) 1) k) =
      Fin.snoc (α := fun _ ↦ ℝ) (Fin.cons (t 0 : ℝ)
        (fun k ↦ (1 - (t 0 : ℝ)) * stickWeights n (Fin.tail t) k)) 0
    rw [← Fin.cons_snoc_eq_snoc_cons, ih, snoc_mul]

/-- The exact final-upper-face equation. -/
theorem stickBreaking_upper_last (n : ℕ) (t : Fin n → I) :
    stickBreaking (n + 1) (Fin.snoc t 1) =
      stdSimplex.map (Fin.last (n + 1)).succAbove (stickBreaking n t) := by
  apply stdSimplex.ext
  ext k
  rw [map_succAbove_weights, Fin.insertNth_last']
  exact congrFun (stickWeights_snoc_one n t) k

/-- The first upper face really collapses, so already q₂ is not injective. -/
theorem stickBreaking_two_not_injective : ¬ Function.Injective (stickBreaking 2) := by
  intro h
  have heq : stickBreaking 2 ![1, 0] = stickBreaking 2 ![1, 1] := by
    apply stdSimplex.ext
    ext k
    refine Fin.cases (by rfl) (fun i ↦ ?_) k
    simp
  have htu := congrFun (h heq) 1
  simp at htu

end Cube
