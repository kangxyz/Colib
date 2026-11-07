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

namespace Convexity.StdSimplex

/-- The first open chart omits the first vertex. -/
def simplexBoundaryLower (n : ℕ) : Set (boundary (n + 1)) :=
  {x | x.val.weights 0 < 1}

/-- The second open chart is the open star of the first vertex. -/
def simplexBoundaryUpper (n : ℕ) : Set (boundary (n + 1)) :=
  {x | 0 < x.val.weights 0}

/-- The overlap of the two vertex charts. -/
def simplexBoundaryOverlap (n : ℕ) : Set (boundary (n + 1)) :=
  simplexBoundaryLower n ∩ simplexBoundaryUpper n

@[fun_prop]
theorem continuous_simplexBoundary_firstWeight (n : ℕ) :
    Continuous (fun x : boundary (n + 1) ↦ x.val.weights 0) :=
  (StdSimplex.continuous_weights_apply ℝ 0).comp continuous_subtype_val

theorem isOpen_simplexBoundaryLower (n : ℕ) : IsOpen (simplexBoundaryLower n) :=
  isOpen_lt (continuous_simplexBoundary_firstWeight n) continuous_const

theorem isOpen_simplexBoundaryUpper (n : ℕ) : IsOpen (simplexBoundaryUpper n) :=
  isOpen_lt continuous_const (continuous_simplexBoundary_firstWeight n)

theorem simplexBoundaryLower_union_upper (n : ℕ) :
    simplexBoundaryLower n ∪ simplexBoundaryUpper n = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro x
  by_cases h : x.val.weights 0 < 1
  · exact Or.inl h
  · exact Or.inr (lt_of_lt_of_le (by norm_num) (le_of_not_gt h))

/-- Remaining barycentric mass is one minus the first coordinate. -/
theorem sum_simplexBoundary_tail {n : ℕ} (x : StdSimplex ℝ (Fin (n + 2))) :
    ∑ i : Fin (n + 1), x.weights i.succ = 1 - x.weights 0 := by
  have h := x.total_of_fintype
  rw [Fin.sum_univ_succ] at h
  linarith

/-- Normalize all coordinates other than the first. -/
def simplexBoundaryTail {n : ℕ} (x : StdSimplex ℝ (Fin (n + 2)))
    (hx : x.weights 0 < 1) : StdSimplex ℝ (Fin (n + 1)) where
  weights := Finsupp.equivFunOnFinite.symm (fun i ↦ x.weights i.succ / (1 - x.weights 0))
  nonneg i := div_nonneg (x.weights_nonneg i.succ) (by linarith)
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    change (∑ i : Fin (n + 1), x.weights i.succ / (1 - x.weights 0)) = 1
    simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul, sum_simplexBoundary_tail]
    exact mul_inv_cancel₀ (by linarith)

@[simp]
theorem simplexBoundaryTail_weights {n : ℕ} (x : StdSimplex ℝ (Fin (n + 2)))
    (hx : x.weights 0 < 1) (i : Fin (n + 1)) :
    (simplexBoundaryTail x hx).weights i = x.weights i.succ / (1 - x.weights 0) := rfl

@[fun_prop]
theorem continuous_simplexBoundaryTail (n : ℕ) :
    Continuous (fun x : {x : StdSimplex ℝ (Fin (n + 2)) // x.weights 0 < 1} ↦
      simplexBoundaryTail x.val x.property) := by
  rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).continuous_iff]
  refine continuous_pi fun i ↦ ?_
  change Continuous (fun x : {x : StdSimplex ℝ (Fin (n + 2)) // x.weights 0 < 1} ↦
    x.val.weights i.succ / (1 - x.val.weights 0))
  apply Continuous.div
  · exact (StdSimplex.continuous_weights_apply ℝ i.succ).comp continuous_subtype_val
  · exact continuous_const.sub
      ((StdSimplex.continuous_weights_apply ℝ 0).comp continuous_subtype_val)
  · intro x
    linarith [x.property]

/-- Add a first coordinate with the specified mass, rescaling the others. -/
def simplexBoundaryCone {n : ℕ} (t : I) (x : StdSimplex ℝ (Fin (n + 1))) :
    StdSimplex ℝ (Fin (n + 2)) where
  weights := Finsupp.equivFunOnFinite.symm
    (Fin.cases (t : ℝ) (fun i ↦ (1 - t) * x.weights i))
  nonneg i := by
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact t.property.1
    · exact mul_nonneg (sub_nonneg.mpr t.property.2) (x.weights_nonneg j)
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    change (∑ i : Fin (n + 2), Fin.cases (motive := fun _ ↦ ℝ) (t : ℝ)
      (fun j ↦ (1 - (t : ℝ)) * x.weights j) i) = 1
    simp only [Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ, ← Finset.mul_sum,
      StdSimplex.total_of_fintype, mul_one]
    ring

@[simp]
theorem simplexBoundaryCone_weights_zero {n : ℕ} (t : I)
    (x : StdSimplex ℝ (Fin (n + 1))) : (simplexBoundaryCone t x).weights 0 = t := rfl

@[simp]
theorem simplexBoundaryCone_weights_succ {n : ℕ} (t : I)
    (x : StdSimplex ℝ (Fin (n + 1))) (i : Fin (n + 1)) :
    (simplexBoundaryCone t x).weights i.succ = (1 - t) * x.weights i := rfl

@[fun_prop]
theorem continuous_simplexBoundaryCone (n : ℕ) :
    Continuous (fun z : I × StdSimplex ℝ (Fin (n + 1)) ↦ simplexBoundaryCone z.1 z.2) := by
  rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 2))).continuous_iff]
  refine continuous_pi fun i ↦ ?_
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · change Continuous (fun z : I × StdSimplex ℝ (Fin (n + 1)) ↦ (z.1 : ℝ))
    exact continuous_subtype_val.comp continuous_fst
  · change Continuous (fun z : I × StdSimplex ℝ (Fin (n + 1)) ↦
      (1 - (z.1 : ℝ)) * z.2.weights j)
    exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      ((StdSimplex.continuous_weights_apply ℝ j).comp continuous_snd)

/-- Normalization exactly inverts the rescaling when the first mass is below one. -/
@[simp]
theorem simplexBoundaryTail_cone {n : ℕ} (t : I) (ht : (t : ℝ) < 1)
    (x : StdSimplex ℝ (Fin (n + 1))) :
    simplexBoundaryTail (simplexBoundaryCone t x) ht = x := by
  apply StdSimplex.ext
  ext i
  change (1 - (t : ℝ)) * x.weights i / (1 - t) = x.weights i
  exact mul_div_cancel_left₀ _ (by linarith)

/-- Restoring the first mass recovers the original simplex point. -/
theorem simplexBoundaryCone_tail {n : ℕ} (x : StdSimplex ℝ (Fin (n + 2)))
    (hx : x.weights 0 < 1) :
    simplexBoundaryCone ⟨x.weights 0, x.weights_nonneg 0, x.weights_apply_le_one 0⟩
      (simplexBoundaryTail x hx) = x := by
  apply StdSimplex.ext
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rfl
  · change (1 - x.weights 0) * (x.weights j.succ / (1 - x.weights 0)) = x.weights j.succ
    field_simp [show 1 - x.weights 0 ≠ 0 by linarith]

/-- The opposite face lies in the boundary because its first coordinate is zero. -/
theorem simplexBoundaryCone_zero_mem {n : ℕ} (x : StdSimplex ℝ (Fin (n + 1))) :
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
    (hx : x.val.weights 0 < 1) (t : I) (ht : x.val.weights 0 = 0 → (t : ℝ) = 0) :
    simplexBoundaryCone t (simplexBoundaryTail x.val hx) ∈ boundary (n + 1) := by
  obtain ⟨i, hi⟩ := x.property
  refine Fin.cases ?_ (fun j hj ↦ ?_) i hi
  · intro h
    exact ⟨0, ht h⟩
  · exact ⟨j.succ, by simp [hj]⟩

end Convexity.StdSimplex
