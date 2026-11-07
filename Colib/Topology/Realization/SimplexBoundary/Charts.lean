/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Analysis.Convex.StdSimplex.BoundaryRetraction
public import Mathlib.Topology.Homotopy.Equiv

/-!
Adapted from `Quillen/Topology/Realization/SimplexBoundaryCharts.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original maps.

# The two vertex charts on the boundary of a simplex

The boundary of `Δ[n+1]` is covered by the open sets where the first coordinate
is less than one and where it is positive. Normalizing the remaining coordinates
on the first chart gives a point of `Δ[n]`; on the intersection it gives a point
of `∂Δ[n]`. The inverse coordinate formula is the explicit simplex cone.
-/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open scoped BigOperators unitInterval

namespace stdSimplex

/-- The first open chart omits the first vertex. -/
def simplexBoundaryLower (n : ℕ) : Set (boundary (n + 1)) :=
  {x | x.val 0 < 1}

/-- The second open chart is the open star of the first vertex. -/
def simplexBoundaryUpper (n : ℕ) : Set (boundary (n + 1)) :=
  {x | 0 < x.val 0}

/-- The overlap of the two vertex charts. -/
def simplexBoundaryOverlap (n : ℕ) : Set (boundary (n + 1)) :=
  simplexBoundaryLower n ∩ simplexBoundaryUpper n

@[fun_prop]
theorem continuous_simplexBoundary_firstWeight (n : ℕ) :
    Continuous (fun x : boundary (n + 1) ↦ x.val 0) :=
  ((continuous_apply 0).comp continuous_subtype_val).comp continuous_subtype_val

theorem isOpen_simplexBoundaryLower (n : ℕ) : IsOpen (simplexBoundaryLower n) :=
  isOpen_lt (continuous_simplexBoundary_firstWeight n) continuous_const

theorem isOpen_simplexBoundaryUpper (n : ℕ) : IsOpen (simplexBoundaryUpper n) :=
  isOpen_lt continuous_const (continuous_simplexBoundary_firstWeight n)

theorem simplexBoundaryLower_union_upper (n : ℕ) :
    simplexBoundaryLower n ∪ simplexBoundaryUpper n = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro x
  by_cases h : x.val 0 < 1
  · exact Or.inl h
  · exact Or.inr (lt_of_lt_of_le (by norm_num) (le_of_not_gt h))

/-- Remaining barycentric mass is one minus the first coordinate. -/
theorem sum_simplexBoundary_tail {n : ℕ} (x : _root_.stdSimplex ℝ (Fin (n + 2))) :
    ∑ i : Fin (n + 1), x i.succ = 1 - x 0 := by
  have h := stdSimplex.sum_eq_one x
  rw [Fin.sum_univ_succ] at h
  linarith

/-- Normalize all coordinates other than the first. -/
def simplexBoundaryTail {n : ℕ} (x : _root_.stdSimplex ℝ (Fin (n + 2)))
    (hx : x 0 < 1) : _root_.stdSimplex ℝ (Fin (n + 1)) :=
  ⟨fun i ↦ x i.succ / (1 - x 0),
    fun i ↦ div_nonneg (stdSimplex.zero_le x i.succ) (by linarith), by
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul, sum_simplexBoundary_tail]
      exact mul_inv_cancel₀ (by linarith)⟩

@[simp]
theorem simplexBoundaryTail_weights {n : ℕ} (x : _root_.stdSimplex ℝ (Fin (n + 2)))
    (hx : x 0 < 1) (i : Fin (n + 1)) :
    (simplexBoundaryTail x hx) i = x i.succ / (1 - x 0) := rfl

@[fun_prop]
theorem continuous_simplexBoundaryTail (n : ℕ) :
    Continuous (fun x : {x : _root_.stdSimplex ℝ (Fin (n + 2)) // x 0 < 1} ↦
      simplexBoundaryTail x.val x.property) := by
  apply Continuous.subtype_mk
  refine continuous_pi fun i ↦ ?_
  change Continuous (fun x : {x : _root_.stdSimplex ℝ (Fin (n + 2)) // x 0 < 1} ↦
    x.val i.succ / (1 - x.val 0))
  apply Continuous.div
  · exact ((continuous_apply i.succ).comp continuous_subtype_val).comp continuous_subtype_val
  · exact continuous_const.sub
      (((continuous_apply 0).comp continuous_subtype_val).comp continuous_subtype_val)
  · intro x
    linarith [x.property]

/-- Add a first coordinate with the specified mass, rescaling the others. -/
def simplexBoundaryCone {n : ℕ} (t : I) (x : _root_.stdSimplex ℝ (Fin (n + 1))) :
    _root_.stdSimplex ℝ (Fin (n + 2)) :=
  ⟨Fin.cases (t : ℝ) (fun i ↦ (1 - t) * x i), (by
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact t.property.1
    · exact mul_nonneg (sub_nonneg.mpr t.property.2) (stdSimplex.zero_le x j)), by
    simp only [Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ, ← Finset.mul_sum,
      stdSimplex.sum_eq_one, mul_one]
    ring⟩

@[simp]
theorem simplexBoundaryCone_weights_zero {n : ℕ} (t : I)
    (x : _root_.stdSimplex ℝ (Fin (n + 1))) : (simplexBoundaryCone t x) 0 = t := rfl

@[simp]
theorem simplexBoundaryCone_weights_succ {n : ℕ} (t : I)
    (x : _root_.stdSimplex ℝ (Fin (n + 1))) (i : Fin (n + 1)) :
    (simplexBoundaryCone t x) i.succ = (1 - t) * x i := rfl

@[fun_prop]
theorem continuous_simplexBoundaryCone (n : ℕ) :
    Continuous (fun z : I × _root_.stdSimplex ℝ (Fin (n + 1)) ↦ simplexBoundaryCone z.1 z.2) := by
  apply Continuous.subtype_mk
  refine continuous_pi fun i ↦ ?_
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · change Continuous (fun z : I × _root_.stdSimplex ℝ (Fin (n + 1)) ↦ (z.1 : ℝ))
    fun_prop
  · change Continuous (fun z : I × _root_.stdSimplex ℝ (Fin (n + 1)) ↦
      (1 - (z.1 : ℝ)) * z.2 j)
    exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      (((continuous_apply j).comp continuous_subtype_val).comp continuous_snd)

/-- Normalization exactly inverts the rescaling when the first mass is below one. -/
@[simp]
theorem simplexBoundaryTail_cone {n : ℕ} (t : I) (ht : (t : ℝ) < 1)
    (x : _root_.stdSimplex ℝ (Fin (n + 1))) :
    simplexBoundaryTail (simplexBoundaryCone t x) ht = x := by
  apply Subtype.ext
  funext i
  change (1 - (t : ℝ)) * x i / (1 - t) = x i
  exact mul_div_cancel_left₀ _ (by linarith)

/-- Restoring the first mass recovers the original simplex point. -/
theorem simplexBoundaryCone_tail {n : ℕ} (x : _root_.stdSimplex ℝ (Fin (n + 2)))
    (hx : x 0 < 1) :
    simplexBoundaryCone ⟨x 0, stdSimplex.zero_le x 0, stdSimplex.le_one x 0⟩
      (simplexBoundaryTail x hx) = x := by
  apply Subtype.ext
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rfl
  · change (1 - x 0) * (x j.succ / (1 - x 0)) = x j.succ
    field_simp [show 1 - x 0 ≠ 0 by linarith]

/-- The opposite face lies in the boundary because its first coordinate is zero. -/
theorem simplexBoundaryCone_zero_mem {n : ℕ} (x : _root_.stdSimplex ℝ (Fin (n + 1))) :
    simplexBoundaryCone 0 x ∈ boundary (n + 1) :=
  ⟨0, rfl⟩

/-- Coning a boundary point stays in the boundary at every height. -/
theorem simplexBoundaryCone_mem {n : ℕ} (t : I) (x : boundary n) :
    simplexBoundaryCone t x.val ∈ boundary (n + 1) := by
  obtain ⟨i, hi⟩ := x.property
  exact ⟨i.succ, by simp [hi]⟩

/-- On the overlap the normalized tail has an actual zero coordinate. -/
theorem simplexBoundaryTail_mem {n : ℕ} (x : simplexBoundaryOverlap n) :
    simplexBoundaryTail x.val.val x.property.1 ∈ boundary n := by
  obtain ⟨i, hi⟩ := x.val.property
  refine Fin.cases ?_ (fun j hj ↦ ?_) i hi
  · intro h
    exact False.elim ((ne_of_gt x.property.2) h)
  · exact ⟨j, by simp [hj]⟩

/-- Moving only the first mass preserves the boundary whenever a zero first
coordinate is kept zero. -/
theorem simplexBoundaryCone_tail_mem {n : ℕ} (x : boundary (n + 1))
    (hx : x.val 0 < 1) (t : I) (ht : x.val 0 = 0 → (t : ℝ) = 0) :
    simplexBoundaryCone t (simplexBoundaryTail x.val hx) ∈ boundary (n + 1) := by
  obtain ⟨i, hi⟩ := x.property
  refine Fin.cases ?_ (fun j hj ↦ ?_) i hi
  · intro h
    exact ⟨0, ht h⟩
  · exact ⟨j.succ, by simp [hj]⟩

end stdSimplex
