/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.SimplexBoundary.Charts
public import Colib.Topology.Realization.SimplexCharts

/-!
Adapted from `Quillen/Topology/Realization/SimplexBoundaryChartsHomotopy.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original maps.

# Explicit deformation equivalences for the simplex-boundary charts

The chart omitting the first vertex retracts to the opposite face. The open
star contracts to the first vertex. The overlap retracts to its section at first
coordinate `1/2`, which is an actual copy of the lower-dimensional boundary.
Every equivalence below is constructed from explicit barycentric formulas.
-/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open scoped BigOperators unitInterval

namespace stdSimplex

/-- Projection from the lower chart to the normalized opposite face. -/
def simplexBoundaryLowerProjection (n : ℕ) :
    C(simplexBoundaryLower n, _root_.stdSimplex ℝ (Fin (n + 1))) where
  toFun x := simplexBoundaryTail x.val.val x.property
  continuous_toFun := (continuous_simplexBoundaryTail n).comp
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk (fun x ↦ x.property))

/-- The opposite face as the zero-height section of the lower chart. -/
def simplexBoundaryLowerSection (n : ℕ) :
    C(_root_.stdSimplex ℝ (Fin (n + 1)), simplexBoundaryLower n) where
  toFun x := ⟨⟨simplexBoundaryCone 0 x, simplexBoundaryCone_zero_mem x⟩, by
    change (0 : ℝ) < 1
    norm_num⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (continuous_simplexBoundaryCone n).comp (continuous_const.prodMk continuous_id)

/-- The first coordinate in the deformation from the opposite face. -/
def simplexBoundaryLowerHeight {n : ℕ} (z : I × simplexBoundaryLower n) : I :=
  ⟨(z.1 : ℝ) * z.2.val.val 0,
    mul_nonneg z.1.property.1 (stdSimplex.zero_le z.2.val.val 0), by
      calc
        (z.1 : ℝ) * z.2.val.val 0 ≤ 1 * z.2.val.val 0 :=
          mul_le_mul_of_nonneg_right z.1.property.2 (stdSimplex.zero_le z.2.val.val 0)
        _ ≤ 1 := by simpa only [one_mul] using stdSimplex.le_one z.2.val.val 0⟩

@[fun_prop]
theorem continuous_simplexBoundaryLowerHeight (n : ℕ) :
    Continuous (simplexBoundaryLowerHeight (n := n)) := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp continuous_fst).mul
    (((continuous_apply 0).comp continuous_subtype_val).comp
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)))

/-- The lower chart deforms from its actual opposite-face section to the identity. -/
def simplexBoundaryLowerHomotopy (n : ℕ) :
    ((simplexBoundaryLowerSection n).comp (simplexBoundaryLowerProjection n)).Homotopy
      (ContinuousMap.id _) where
  toFun z := ⟨⟨simplexBoundaryCone (simplexBoundaryLowerHeight z)
      (simplexBoundaryTail z.2.val.val z.2.property),
    simplexBoundaryCone_tail_mem z.2.val z.2.property _ (by
      intro h
      change (z.1 : ℝ) * z.2.val.val 0 = 0
      simp [h])⟩, by
        change (z.1 : ℝ) * z.2.val.val 0 < 1
        have h := z.2.property
        change z.2.val.val 0 < 1 at h
        calc
          (z.1 : ℝ) * z.2.val.val 0 ≤ 1 * z.2.val.val 0 :=
            mul_le_mul_of_nonneg_right z.1.property.2 (stdSimplex.zero_le z.2.val.val 0)
          _ < 1 := by simpa using h⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (continuous_simplexBoundaryCone n).comp
      ((continuous_simplexBoundaryLowerHeight n).prodMk
        ((simplexBoundaryLowerProjection n).continuous.comp continuous_snd))
  map_zero_left x := by
    apply Subtype.ext
    apply Subtype.ext
    change simplexBoundaryCone (simplexBoundaryLowerHeight (0, x))
      (simplexBoundaryTail x.val.val x.property) =
        simplexBoundaryCone 0 (simplexBoundaryTail x.val.val x.property)
    congr 1
    apply Subtype.ext
    simp [simplexBoundaryLowerHeight]
  map_one_left x := by
    apply Subtype.ext
    apply Subtype.ext
    change simplexBoundaryCone (simplexBoundaryLowerHeight (1, x))
      (simplexBoundaryTail x.val.val x.property) = x.val.val
    have ht : simplexBoundaryLowerHeight (1, x) =
        ⟨x.val.val 0, stdSimplex.zero_le x.val.val 0, stdSimplex.le_one x.val.val 0⟩ := by
      apply Subtype.ext
      simp [simplexBoundaryLowerHeight]
    rw [ht]
    exact simplexBoundaryCone_tail x.val.val x.property

/-- The lower open chart is homotopy equivalent to the actual opposite simplex. -/
def simplexBoundaryLowerEquiv (n : ℕ) :
    ContinuousMap.HomotopyEquiv (simplexBoundaryLower n) (_root_.stdSimplex ℝ (Fin (n + 1))) where
  toFun := simplexBoundaryLowerProjection n
  invFun := simplexBoundaryLowerSection n
  left_inv := ⟨simplexBoundaryLowerHomotopy n⟩
  right_inv := by
    have h : (simplexBoundaryLowerProjection n).comp (simplexBoundaryLowerSection n) =
        ContinuousMap.id _ := by
      apply ContinuousMap.ext
      intro x
      exact simplexBoundaryTail_cone 0 (by norm_num) x
    rw [h]

/-- The original first vertex lies in its open star and in the boundary. -/
def simplexBoundaryUpperVertex (n : ℕ) : simplexBoundaryUpper n :=
  ⟨⟨stdSimplex.vertex 0, ⟨(0 : Fin (n + 1)).succ, by
    change (Pi.single (M := fun _ : Fin (n + 2) ↦ ℝ) 0 (1 : ℝ)) (0 : Fin (n + 1)).succ = 0
    simp⟩⟩, by
    change (0 : ℝ) < 1
    norm_num⟩

/-- The affine contraction of the open star, with its actual boundary proof. -/
def simplexBoundaryUpperHomotopy (n : ℕ) :
    (ContinuousMap.const (simplexBoundaryUpper n) (simplexBoundaryUpperVertex n)).Homotopy
      (ContinuousMap.id _) where
  toFun z := ⟨⟨simplexSegment (stdSimplex.vertex 0) z.2.val.val z.1, by
    obtain ⟨i, hi⟩ := z.2.val.property
    have hi0 : i ≠ 0 := by
      intro h
      subst i
      exact (ne_of_gt z.2.property) hi
    refine ⟨i, ?_⟩
    change (1 - (z.1 : ℝ)) * (Pi.single (M := fun _ : Fin (n + 2) ↦ ℝ) 0 (1 : ℝ)) i +
      (z.1 : ℝ) * z.2.val.val i = 0
    simp [hi, hi0]⟩, by
      change 0 < simplexSegment (stdSimplex.vertex 0) z.2.val.val z.1 0
      change 0 < (1 - (z.1 : ℝ)) * 1 + (z.1 : ℝ) * z.2.val.val 0
      rw [mul_one]
      have h := z.2.property
      change 0 < z.2.val.val 0 at h
      by_cases hs : (z.1 : ℝ) < 1
      · have hm := mul_nonneg z.1.property.1 (le_of_lt h)
        linarith
      · have hs' : (z.1 : ℝ) = 1 := le_antisymm z.1.property.2 (le_of_not_gt hs)
        simpa only [hs', sub_self, one_mul, zero_add] using h⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    refine continuous_pi fun i ↦ ?_
    change Continuous (fun z : I × simplexBoundaryUpper n ↦
      (1 - (z.1 : ℝ)) * stdSimplex.vertex (S := ℝ) (0 : Fin (n + 2)) i +
        (z.1 : ℝ) * z.2.val.val i)
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      continuous_const).add
      ((continuous_subtype_val.comp continuous_fst).mul
        (((continuous_apply i).comp continuous_subtype_val).comp
          (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))))
  map_zero_left x := by
    apply Subtype.ext
    apply Subtype.ext
    exact (simplexSegment _ _).source
  map_one_left x := by
    apply Subtype.ext
    apply Subtype.ext
    exact (simplexSegment _ _).target

/-- The upper open chart is explicitly contractible. -/
def simplexBoundaryUpperEquiv (n : ℕ) :
    ContinuousMap.HomotopyEquiv (simplexBoundaryUpper n) PUnit where
  toFun := ContinuousMap.const _ PUnit.unit
  invFun := ContinuousMap.const _ (simplexBoundaryUpperVertex n)
  left_inv := ⟨simplexBoundaryUpperHomotopy n⟩
  right_inv := by
    have h : (ContinuousMap.const (simplexBoundaryUpper n) PUnit.unit).comp
        (ContinuousMap.const PUnit (simplexBoundaryUpperVertex n)) = ContinuousMap.id _ := by
      apply ContinuousMap.ext
      intro x
      exact Subsingleton.elim _ _
    rw [h]

/-- The midpoint height used for the overlap section. -/
def simplexBoundaryMidpoint : I := ⟨1 / 2, by norm_num, by norm_num⟩

/-- The normalized boundary point in the overlap. -/
def simplexBoundaryOverlapProjection (n : ℕ) : C(simplexBoundaryOverlap n, boundary n) where
  toFun x := ⟨simplexBoundaryTail x.val.val x.property.1, simplexBoundaryTail_mem x⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_simplexBoundaryTail n).comp
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk
        (fun x ↦ x.property.1))

/-- The actual lower-dimensional boundary at first coordinate `1/2`. -/
def simplexBoundaryOverlapSection (n : ℕ) : C(boundary n, simplexBoundaryOverlap n) where
  toFun x := ⟨⟨simplexBoundaryCone simplexBoundaryMidpoint x.val,
    simplexBoundaryCone_mem simplexBoundaryMidpoint x⟩, by
      constructor <;> change (_ : ℝ) < _ <;> norm_num [simplexBoundaryMidpoint]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (continuous_simplexBoundaryCone n).comp
      (continuous_const.prodMk continuous_subtype_val)

/-- Linear motion of the first mass from `1/2` to its original value. -/
def simplexBoundaryOverlapHeight {n : ℕ} (z : I × simplexBoundaryOverlap n) : I :=
  ⟨(1 - (z.1 : ℝ)) / 2 + (z.1 : ℝ) * z.2.val.val 0, by
      exact add_nonneg (div_nonneg (sub_nonneg.mpr z.1.property.2) (by norm_num))
        (mul_nonneg z.1.property.1 (stdSimplex.zero_le z.2.val.val 0)), by
      have h := mul_le_mul_of_nonneg_left (stdSimplex.le_one z.2.val.val 0) z.1.property.1
      nlinarith [z.1.property.2]⟩

@[fun_prop]
theorem continuous_simplexBoundaryOverlapHeight (n : ℕ) :
    Continuous (simplexBoundaryOverlapHeight (n := n)) := by
  apply Continuous.subtype_mk
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).div_const 2).add
    ((continuous_subtype_val.comp continuous_fst).mul
      (((continuous_apply 0).comp continuous_subtype_val).comp
        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))))

/-- The overlap deforms from the midpoint boundary section to the identity. -/
def simplexBoundaryOverlapHomotopy (n : ℕ) :
    ((simplexBoundaryOverlapSection n).comp (simplexBoundaryOverlapProjection n)).Homotopy
      (ContinuousMap.id _) where
  toFun z := ⟨⟨simplexBoundaryCone (simplexBoundaryOverlapHeight z)
      (simplexBoundaryOverlapProjection n z.2).val,
    simplexBoundaryCone_mem _ (simplexBoundaryOverlapProjection n z.2)⟩, by
      have h₀ := z.2.property.2
      have h₁ := z.2.property.1
      change 0 < z.2.val.val 0 at h₀
      change z.2.val.val 0 < 1 at h₁
      constructor
      · change (1 - (z.1 : ℝ)) / 2 + (z.1 : ℝ) * z.2.val.val 0 < 1
        by_cases hs : (z.1 : ℝ) < 1
        · have hm := mul_le_mul_of_nonneg_left (le_of_lt h₁) z.1.property.1
          nlinarith
        · have hs' : (z.1 : ℝ) = 1 := le_antisymm z.1.property.2 (le_of_not_gt hs)
          simpa [hs'] using h₁
      · change 0 < (1 - (z.1 : ℝ)) / 2 + (z.1 : ℝ) * z.2.val.val 0
        by_cases hs : (z.1 : ℝ) < 1
        · have hm := mul_nonneg z.1.property.1 (le_of_lt h₀)
          linarith
        · have hs' : (z.1 : ℝ) = 1 := le_antisymm z.1.property.2 (le_of_not_gt hs)
          simpa [hs'] using h₀⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (continuous_simplexBoundaryCone n).comp
      ((continuous_simplexBoundaryOverlapHeight n).prodMk
        (continuous_subtype_val.comp
          ((simplexBoundaryOverlapProjection n).continuous.comp continuous_snd)))
  map_zero_left x := by
    apply Subtype.ext
    apply Subtype.ext
    change simplexBoundaryCone (simplexBoundaryOverlapHeight (0, x))
      (simplexBoundaryOverlapProjection n x).val =
        simplexBoundaryCone simplexBoundaryMidpoint (simplexBoundaryOverlapProjection n x).val
    congr 1
    apply Subtype.ext
    simp [simplexBoundaryOverlapHeight, simplexBoundaryMidpoint]
  map_one_left x := by
    apply Subtype.ext
    apply Subtype.ext
    change simplexBoundaryCone (simplexBoundaryOverlapHeight (1, x))
      (simplexBoundaryTail x.val.val x.property.1) = x.val.val
    have ht : simplexBoundaryOverlapHeight (1, x) =
        ⟨x.val.val 0, stdSimplex.zero_le x.val.val 0, stdSimplex.le_one x.val.val 0⟩ := by
      apply Subtype.ext
      simp [simplexBoundaryOverlapHeight]
    rw [ht]
    exact simplexBoundaryCone_tail x.val.val x.property.1

/-- The actual overlap is homotopy equivalent to the lower-dimensional boundary.
For `n = 0` both sides are empty; the same formulas remain valid. -/
def simplexBoundaryOverlapEquiv (n : ℕ) :
    ContinuousMap.HomotopyEquiv (simplexBoundaryOverlap n) (boundary n) where
  toFun := simplexBoundaryOverlapProjection n
  invFun := simplexBoundaryOverlapSection n
  left_inv := ⟨simplexBoundaryOverlapHomotopy n⟩
  right_inv := by
    have h : (simplexBoundaryOverlapProjection n).comp (simplexBoundaryOverlapSection n) =
        ContinuousMap.id _ := by
      apply ContinuousMap.ext
      intro x
      apply Subtype.ext
      exact simplexBoundaryTail_cone simplexBoundaryMidpoint (by norm_num [simplexBoundaryMidpoint])
        x.val
    rw [h]

end stdSimplex
