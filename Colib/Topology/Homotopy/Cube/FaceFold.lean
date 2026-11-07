/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.Cube.Rotation

/-!
# Moving a lateral cube face into the top face

An explicit homotopy of the square fixes its bottom and right sides, shrinks
its left side, and extends its top side around the vacated left edge. At the
last time the left edge is collapsed and the top edge first traverses the old
left edge, then the old top edge, in exactly equal parameter intervals.

The homotopy preserves the square boundary at every time. It need not preserve
each corner during the homotopy; it does preserve corners at the final time.
This distinction is essential when the construction is inserted into a higher
cube: unaffected faces have genuine boundary-relative homotopies, whereas the
folded top face changes by the original cubical concatenation.
-/

/-! Implementation source: `Quillen/Topology/Cube/FaceFold.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual cubical maps,
relative homotopies, quotient multiplication, and signs are retained. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval

namespace Topology

/-- Horizontal position of the expanding top-edge path. -/
def faceFoldTopX (r s : I) : ℝ := max ((1 + (r : ℝ)) * s - r) 0

/-- Vertical position of the expanding top-edge path. -/
def faceFoldTopY (r s : I) : ℝ := min (1 - (r : ℝ) + (1 + r) * s) 1

theorem faceFoldTopX_mem (r s : I) : faceFoldTopX r s ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨le_max_right _ _, max_le ?_ zero_le_one⟩
  have h := mul_nonneg (show 0 ≤ 1 + (r : ℝ) by linarith [r.property.1])
    (sub_nonneg.mpr s.property.2)
  nlinarith

theorem faceFoldTopY_mem (r s : I) : faceFoldTopY r s ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨le_min ?_ zero_le_one, min_le_right _ _⟩
  exact add_nonneg (sub_nonneg.mpr r.property.2)
    (mul_nonneg (by linarith [r.property.1]) s.property.1)

@[fun_prop] theorem continuous_faceFoldTopX :
    Continuous (fun p : I × I ↦ faceFoldTopX p.1 p.2) := by
  unfold faceFoldTopX
  fun_prop

@[fun_prop] theorem continuous_faceFoldTopY :
    Continuous (fun p : I × I ↦ faceFoldTopY p.1 p.2) := by
  unfold faceFoldTopY
  fun_prop

/-- The full continuous square fold at a displayed time. -/
def faceFold (r : I) (p : I × I) : I × I :=
  (⟨(1 - (p.2 : ℝ)) * p.1 + p.2 * faceFoldTopX r p.1, by
    constructor
    · exact add_nonneg
        (mul_nonneg (sub_nonneg.mpr p.2.property.2) p.1.property.1)
        (mul_nonneg p.2.property.1 (faceFoldTopX_mem r p.1).1)
    · have h₁ := mul_nonneg (sub_nonneg.mpr p.2.property.2)
        (sub_nonneg.mpr p.1.property.2)
      have h₂ := mul_nonneg p.2.property.1 (sub_nonneg.mpr (faceFoldTopX_mem r p.1).2)
      nlinarith⟩,
    ⟨(p.2 : ℝ) * faceFoldTopY r p.1, by
      constructor
      · exact mul_nonneg p.2.property.1 (faceFoldTopY_mem r p.1).1
      · have h := mul_nonneg p.2.property.1 (sub_nonneg.mpr (faceFoldTopY_mem r p.1).2)
        have := p.2.property.2
        nlinarith⟩)

@[simp] theorem faceFold_fst (r : I) (p : I × I) :
    ((faceFold r p).1 : ℝ) =
      (1 - (p.2 : ℝ)) * p.1 + p.2 * faceFoldTopX r p.1 := rfl

@[simp] theorem faceFold_snd (r : I) (p : I × I) :
    ((faceFold r p).2 : ℝ) = (p.2 : ℝ) * faceFoldTopY r p.1 := rfl

@[fun_prop] theorem continuous_faceFold :
    Continuous (fun p : I × (I × I) ↦ faceFold p.1 p.2) := by
  unfold faceFold
  apply Continuous.prodMk <;> apply Continuous.subtype_mk
  · fun_prop
  · fun_prop

@[simp] theorem faceFoldTopX_zero (s : I) : faceFoldTopX 0 s = s := by
  change max ((1 + (0 : ℝ)) * s - 0) 0 = s
  simp [max_eq_left s.property.1]

@[simp] theorem faceFoldTopY_zero (s : I) : faceFoldTopY 0 s = 1 := by
  change min (1 - (0 : ℝ) + (1 + 0) * s) 1 = 1
  apply min_eq_right
  linarith [s.property.1]

/-- The square homotopy starts at the identity, with both coordinates retained. -/
@[simp] theorem faceFold_zero (p : I × I) : faceFold 0 p = p := by
  apply Prod.ext <;> apply Subtype.ext
  · simp only [faceFold_fst, faceFoldTopX_zero]
    ring
  · simp

/-- The entire bottom edge is fixed at every time. -/
@[simp] theorem faceFold_bottom (r s : I) : faceFold r (s, 0) = (s, 0) := by
  apply Prod.ext <;> apply Subtype.ext <;> simp

/-- The right edge is fixed at every time. -/
@[simp] theorem faceFold_right (r t : I) : faceFold r (1, t) = (1, t) := by
  have hx : faceFoldTopX r 1 = 1 := by
    change max ((1 + (r : ℝ)) * 1 - r) 0 = 1
    rw [show (1 + (r : ℝ)) * 1 - r = 1 by ring]
    norm_num
  have hy : faceFoldTopY r 1 = 1 := by
    change min (1 - (r : ℝ) + (1 + r) * 1) 1 = 1
    apply min_eq_right
    ring_nf
    norm_num
  apply Prod.ext <;> apply Subtype.ext
  · change (1 - (t : ℝ)) * 1 + t * faceFoldTopX r 1 = 1
    rw [hx]
    ring
  · simp [hy]

/-- The left edge contracts within itself. -/
@[simp] theorem faceFold_left_fst (r t : I) : (faceFold r (0, t)).1 = 0 := by
  apply Subtype.ext
  have hx : faceFoldTopX r 0 = 0 := by
    unfold faceFoldTopX
    simp [max_eq_right (neg_nonpos.mpr r.property.1)]
  simp [hx]

/-- At the final time the whole left edge is the bottom-left corner. -/
@[simp] theorem faceFold_one_left (t : I) : faceFold 1 (0, t) = (0, 0) := by
  apply Prod.ext
  · exact faceFold_left_fst 1 t
  · apply Subtype.ext
    simp [faceFoldTopY]

/-- The homotopy preserves the square boundary; corners may move within it. -/
theorem faceFold_boundary (r : I) (p : I × I) (hp : SquareBoundary p) :
    SquareBoundary (faceFold r p) := by
  rcases p with ⟨s, t⟩
  rcases hp with h | h | h | h
  · change s = 0 at h
    subst s
    exact Or.inl (faceFold_left_fst r t)
  · change s = 1 at h
    subst s
    right; left
    simp
  · change t = 0 at h
    subst t
    right; right; left
    simp
  · change t = 1 at h
    subst t
    by_cases hs : (1 + (r : ℝ)) * s ≤ r
    · left
      apply Subtype.ext
      simp [faceFoldTopX, max_eq_right (sub_nonpos.mpr hs)]
    · right; right; right
      apply Subtype.ext
      have hs' : 1 ≤ 1 - (r : ℝ) + (1 + r) * s := by linarith
      simp [faceFoldTopY, min_eq_right hs']

/-- The terminal fold sends corners to corners, restoring codimension-two basedness. -/
theorem faceFold_one_corners (p : I × I)
    (h₁ : p.1 = 0 ∨ p.1 = 1) (h₂ : p.2 = 0 ∨ p.2 = 1) :
    ((faceFold 1 p).1 = 0 ∨ (faceFold 1 p).1 = 1) ∧
      ((faceFold 1 p).2 = 0 ∨ (faceFold 1 p).2 = 1) := by
  rcases p with ⟨s, t⟩
  rcases h₁ with rfl | rfl
  · simp
  · rcases h₂ with rfl | rfl <;> simp

/-- On the first half of the final top edge, the original left edge is traversed upwards. -/
theorem faceFold_one_top_first (s : I) (hs : (s : ℝ) ≤ 1 / 2) :
    faceFold 1 (s, 1) = (0, Set.projIcc (0 : ℝ) 1 zero_le_one (2 * (s : ℝ))) := by
  have hle : 2 * (s : ℝ) ≤ 1 := by linarith
  have hnonneg : 0 ≤ 2 * (s : ℝ) := mul_nonneg (by norm_num) s.property.1
  apply Prod.ext <;> apply Subtype.ext
  · change (1 - (1 : ℝ)) * (s : ℝ) + 1 * max (((1 : ℝ) + 1) * (s : ℝ) - 1) 0 = 0
    norm_num only [sub_self, zero_mul, one_mul, zero_add, show (1 : ℝ) + 1 = 2 by norm_num]
    exact max_eq_right (sub_nonpos.mpr hle)
  · change (1 : ℝ) * min ((1 : ℝ) - 1 + ((1 : ℝ) + 1) * (s : ℝ)) 1 = _
    rw [Set.projIcc_of_mem zero_le_one ⟨hnonneg, hle⟩]
    norm_num only [sub_self, zero_add, one_mul, show (1 : ℝ) + 1 = 2 by norm_num]
    exact min_eq_left hle

/-- On the second half, the original top edge is traversed from left to right. -/
theorem faceFold_one_top_second (s : I) (hs : 1 / 2 ≤ (s : ℝ)) :
    faceFold 1 (s, 1) = (Set.projIcc (0 : ℝ) 1 zero_le_one (2 * (s : ℝ) - 1), 1) := by
  have hnonneg : 0 ≤ 2 * (s : ℝ) - 1 := by linarith
  have hle : 2 * (s : ℝ) - 1 ≤ 1 := by have := s.property.2; linarith
  apply Prod.ext <;> apply Subtype.ext
  · change (1 - (1 : ℝ)) * (s : ℝ) + 1 * max (((1 : ℝ) + 1) * (s : ℝ) - 1) 0 = _
    rw [Set.projIcc_of_mem zero_le_one ⟨hnonneg, hle⟩]
    norm_num only [sub_self, zero_mul, one_mul, zero_add, show (1 : ℝ) + 1 = 2 by norm_num]
    exact max_eq_left hnonneg
  · change (1 : ℝ) * min ((1 : ℝ) - 1 + ((1 : ℝ) + 1) * (s : ℝ)) 1 = 1
    norm_num only [sub_self, zero_add, one_mul, show (1 : ℝ) + 1 = 2 by norm_num]
    exact min_eq_right (by linarith)

end Topology
