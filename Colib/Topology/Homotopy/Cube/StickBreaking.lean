/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Analysis.Convex.StdSimplex.Boundary
public import Mathlib.Topology.Homotopy.HomotopyGroup
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FunProp

/-!
# The explicit stick-breaking cube quotient

The recursive barycentric formula takes `(t, u)` to `(t, (1-t) q(u))`.
It is a continuous surjection with exact boundary preimage and singleton
interior fibres. In positive dimensions it need not be a homeomorphism.
These facts justify descending boundary-constant maps and their homotopies
without assigning an orientation to an existentially chosen homeomorphism.
-/

/-! Implementation source: `Quillen/Topology/Cube/StickBreaking.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original ordered coordinate
formula is implemented directly in native function-subtype singular simplices. -/
@[expose] public section

open Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped BigOperators Topology unitInterval

namespace Cube

/-- The explicit, recursively ordered stick-breaking barycentric weights. -/
def stickWeights : (n : ℕ) → (Fin n → I) → Fin (n + 1) → ℝ
  | 0, _ => fun _ ↦ 1
  | n + 1, t => Fin.cons (t 0 : ℝ)
      (fun j ↦ (1 - (t 0 : ℝ)) * stickWeights n (Fin.tail t) j)

@[simp] theorem stickWeights_zero (t : Fin 0 → I) (i : Fin 1) :
    stickWeights 0 t i = 1 := rfl

@[simp] theorem stickWeights_succ_zero {n : ℕ} (t : Fin (n + 1) → I) :
    stickWeights (n + 1) t 0 = (t 0 : ℝ) := rfl

@[simp] theorem stickWeights_succ_succ {n : ℕ} (t : Fin (n + 1) → I)
    (i : Fin (n + 1)) :
    stickWeights (n + 1) t i.succ =
      (1 - (t 0 : ℝ)) * stickWeights n (Fin.tail t) i := rfl

theorem stickWeights_nonneg (n : ℕ) (t : Fin n → I) (i : Fin (n + 1)) :
    0 ≤ stickWeights n t i := by
  induction n with
  | zero => simp
  | succ n ih =>
    refine Fin.cases (t 0).property.1 (fun j ↦ ?_) i
    exact mul_nonneg (sub_nonneg.mpr (t 0).property.2) (ih _ j)

theorem sum_stickWeights (n : ℕ) (t : Fin n → I) :
    ∑ i, stickWeights n t i = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Fin.sum_univ_succ, stickWeights_succ_zero, stickWeights_succ_succ,
      ← Finset.mul_sum, ih, mul_one]
    ring

/-- The specified cube-to-simplex map, with no chosen disk homeomorphism. -/
def stickBreaking (n : ℕ) (t : Fin n → I) : _root_.stdSimplex ℝ (Fin (n + 1)) :=
  ⟨stickWeights n t, stickWeights_nonneg n t, sum_stickWeights n t⟩

@[simp] theorem stickBreaking_weights (n : ℕ) (t : Fin n → I) (i : Fin (n + 1)) :
    (stickBreaking n t) i = stickWeights n t i := rfl

@[fun_prop] theorem continuous_stickWeights (n : ℕ) (i : Fin (n + 1)) :
    Continuous (fun t : Fin n → I ↦ stickWeights n t i) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact continuous_subtype_val.comp (continuous_apply 0)
    · exact (continuous_const.sub (continuous_subtype_val.comp (continuous_apply 0))).mul
        ((ih j).comp (continuous_pi fun k ↦ continuous_apply k.succ))

@[fun_prop] theorem continuous_stickBreaking (n : ℕ) : Continuous (stickBreaking n) :=
  Continuous.subtype_mk (continuous_pi (continuous_stickWeights n)) _

/-- The continuous map whose formula is fixed in every dimension. -/
def stickBreakingMap (n : ℕ) : C((Fin n → I), _root_.stdSimplex ℝ (Fin (n + 1))) :=
  ⟨stickBreaking n, continuous_stickBreaking n⟩

private theorem cube_boundary_cons_iff {n : ℕ} (a : I) (t : Fin n → I) :
    Fin.cons a t ∈ _root_.Cube.boundary (Fin (n + 1)) ↔
      a = 0 ∨ a = 1 ∨ t ∈ _root_.Cube.boundary (Fin n) := by
  constructor
  · rintro ⟨i, hi⟩
    refine Fin.cases (fun h ↦ ?_) (fun j h ↦ ?_) i hi
    · rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨j, h⟩)
  · rintro (h | h | ⟨i, hi⟩)
    · exact ⟨0, Or.inl h⟩
    · exact ⟨0, Or.inr h⟩
    · exact ⟨i.succ, hi⟩

/-- The simplex boundary has exactly the original cube boundary as its preimage. -/
theorem stickBreaking_mem_boundary_iff (n : ℕ) (t : Fin n → I) :
    stickBreaking n t ∈ stdSimplex.boundary n ↔ t ∈ _root_.Cube.boundary (Fin n) := by
  induction n with
  | zero => simp [stdSimplex.boundary, _root_.Cube.boundary]
  | succ n ih =>
    have ht : t = Fin.cons (t 0) (Fin.tail t) := (Fin.cons_self_tail t).symm
    rw [ht, cube_boundary_cons_iff]
    constructor
    · rintro ⟨i, hi⟩
      refine Fin.cases (fun h ↦ ?_) (fun j h ↦ ?_) i hi
      · exact Or.inl (Subtype.ext h)
      · change (1 - (t 0 : ℝ)) * stickWeights n (Fin.tail t) j = 0 at h
        rcases mul_eq_zero.mp h with h | h
        · exact Or.inr (Or.inl (Subtype.ext (by change (t 0 : ℝ) = 1; linarith)))
        · exact Or.inr (Or.inr ((ih _).mp ⟨j, h⟩))
    · rintro (h | h | h)
      · exact ⟨0, by simpa using congrArg Subtype.val h⟩
      · refine ⟨(0 : Fin (n + 1)).succ, ?_⟩
        change (1 - (t 0 : ℝ)) * stickWeights n (Fin.tail t) 0 = 0
        rw [h]
        simp
      · obtain ⟨i, hi⟩ := (ih _).mpr h
        change stickWeights n (Fin.tail t) i = 0 at hi
        refine ⟨i.succ, ?_⟩
        change (1 - (t 0 : ℝ)) * stickWeights n (Fin.tail t) i = 0
        rw [hi, mul_zero]

private theorem weight_le_one {n : ℕ} (x : _root_.stdSimplex ℝ (Fin (n + 1)))
    (i : Fin (n + 1)) : x i ≤ 1 := by
  rw [← stdSimplex.sum_eq_one x]
  exact Finset.single_le_sum (fun j _ ↦ stdSimplex.zero_le x j) (Finset.mem_univ i)

/-- The ordered barycentric formula covers the entire simplex, including its boundary. -/
theorem stickBreaking_surjective (n : ℕ) : Function.Surjective (stickBreaking n) := by
  induction n with
  | zero =>
    intro x
    refine ⟨fun i ↦ Fin.elim0 i, ?_⟩
    apply stdSimplex.ext
    ext i
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    simp
  | succ n ih =>
    intro x
    let a : I := ⟨x 0, stdSimplex.zero_le x 0, weight_le_one x 0⟩
    by_cases ha : x 0 = 1
    · refine ⟨Fin.cons a (fun _ ↦ 0), ?_⟩
      apply stdSimplex.ext
      ext i
      refine Fin.cases (by rfl) (fun j ↦ ?_) i
      have hsum : ∑ k : Fin (n + 1), x k.succ = 0 := by
        have h := stdSimplex.sum_eq_one x
        rw [Fin.sum_univ_succ, ha] at h
        linarith
      have hj : x j.succ = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun k _ ↦ stdSimplex.zero_le x k.succ)).mp hsum j
          (Finset.mem_univ j)
      simp [a, ha, hj]
    · have hpos : 0 < 1 - x 0 := sub_pos.mpr (lt_of_le_of_ne (weight_le_one x 0) ha)
      let y : _root_.stdSimplex ℝ (Fin (n + 1)) :=
        ⟨fun i ↦ x i.succ / (1 - x 0),
          fun i ↦ div_nonneg (stdSimplex.zero_le x i.succ) hpos.le, by
          change (∑ i : Fin (n + 1), x i.succ / (1 - x 0)) = 1
          simp only [div_eq_mul_inv, ← Finset.sum_mul]
          have h := stdSimplex.sum_eq_one x
          rw [Fin.sum_univ_succ] at h
          rw [show ∑ i : Fin (n + 1), x i.succ = 1 - x 0 by linarith]
          exact mul_inv_cancel₀ (ne_of_gt hpos)⟩
      obtain ⟨t, ht⟩ := ih y
      refine ⟨Fin.cons a t, ?_⟩
      apply stdSimplex.ext
      ext i
      refine Fin.cases (by rfl) (fun j ↦ ?_) i
      have hj := congrArg (fun z : _root_.stdSimplex ℝ (Fin (n + 1)) ↦ z j) ht
      change stickWeights n t j = x j.succ / (1 - x 0) at hj
      change (1 - x 0) * stickWeights n t j = x j.succ
      rw [hj, mul_div_cancel₀ _ (ne_of_gt hpos)]

/-- Compact-to-Hausdorff descent applies to the explicit map. -/
theorem stickBreaking_isQuotientMap (n : ℕ) : IsQuotientMap (stickBreaking n) :=
  IsQuotientMap.of_surjective_continuous (stickBreaking_surjective n) (continuous_stickBreaking n)

/-- Every fibre away from the boundary is a singleton. -/
theorem stickBreaking_eq_imp_of_not_boundary (n : ℕ) {t u : Fin n → I}
    (ht : t ∉ _root_.Cube.boundary (Fin n)) (h : stickBreaking n t = stickBreaking n u) :
    t = u := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    have hhead : t 0 = u 0 := Subtype.ext
      (congrArg (fun x : _root_.stdSimplex ℝ (Fin (n + 2)) ↦ x 0) h)
    have htone : (t 0 : ℝ) ≠ 1 := by
      intro he
      exact ht ⟨0, Or.inr (Subtype.ext he)⟩
    have htail : Fin.tail t ∉ _root_.Cube.boundary (Fin n) := by
      rintro ⟨i, hi⟩
      exact ht ⟨i.succ, hi⟩
    have heq : stickBreaking n (Fin.tail t) = stickBreaking n (Fin.tail u) := by
      apply stdSimplex.ext
      ext i
      have hi := congrArg (fun x : _root_.stdSimplex ℝ (Fin (n + 2)) ↦ x i.succ) h
      change (1 - (t 0 : ℝ)) * stickWeights n (Fin.tail t) i =
        (1 - (u 0 : ℝ)) * stickWeights n (Fin.tail u) i at hi
      rw [← hhead] at hi
      exact mul_left_cancel₀ (sub_ne_zero.mpr (Ne.symm htone)) hi
    have heqtail := ih htail heq
    rw [← Fin.cons_self_tail t, ← Fin.cons_self_tail u, hhead, heqtail]

/-- Distinct points of one fibre both belong to the collapsed boundary. -/
theorem stickBreaking_fibre_boundary {n : ℕ} {t u : Fin n → I}
    (h : stickBreaking n t = stickBreaking n u) :
    t = u ∨ (t ∈ _root_.Cube.boundary (Fin n) ∧ u ∈ _root_.Cube.boundary (Fin n)) := by
  by_cases ht : t ∈ _root_.Cube.boundary (Fin n)
  · exact Or.inr ⟨ht, (stickBreaking_mem_boundary_iff n u).mp
      (h ▸ (stickBreaking_mem_boundary_iff n t).mpr ht)⟩
  · exact Or.inl (stickBreaking_eq_imp_of_not_boundary n ht h)

end Cube
