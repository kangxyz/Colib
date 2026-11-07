/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.Topology.Realization.SimplexCharts

/-!
# The path-connected overlap of simplex collar and interior

A shrunken copy of the boundary lies strictly inside the simplex and still
inside the collar. Every point of the overlap joins that copy by a straight
radial segment which stays in the overlap. Hence the overlap is path-connected
in dimensions at least two.
-/
/-!
## Implementation provenance

Adapted from `Quillen/Topology/Realization/EdgePathPresentation/Annulus.lean`
at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual barycentric
maps, scale 3/4, defect threshold 1/2, and dimension hypotheses are retained.
Only namespace and import ownership change. Interior simple connectedness is
outside this slice.
-/
@[expose] public section


noncomputable section
open Set
open scoped Topology unitInterval BigOperators

namespace stdSimplex

/-- Shrink a simplex toward its barycenter by the fixed radial factor `3/4`. -/
def simplexInnerScale {n : ℕ} (x : _root_.stdSimplex ℝ (Fin (n + 1))) :
    _root_.stdSimplex ℝ (Fin (n + 1)) :=
  simplexSegment stdSimplex.barycenter x ⟨3 / 4, by norm_num, by norm_num⟩

@[simp] theorem simplexInnerScale_weights {n : ℕ}
    (x : _root_.stdSimplex ℝ (Fin (n + 1))) (i : Fin (n + 1)) :
    (simplexInnerScale x) i =
      (1 / 4 : ℝ) * (1 / (n + 1)) + (3 / 4 : ℝ) * x i := by
  change (1 - (3 / 4 : ℝ)) * (Fintype.card (Fin (n + 1)) : ℝ)⁻¹ +
    (3 / 4 : ℝ) * x i = (1 / 4 : ℝ) * (1 / (n + 1)) + (3 / 4 : ℝ) * x i
  norm_num [Fintype.card_fin, Nat.cast_add, Nat.cast_one, one_div]

@[fun_prop] theorem continuous_simplexInnerScale {n : ℕ} :
    Continuous (simplexInnerScale (n := n)) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  change Continuous (fun x : _root_.stdSimplex ℝ (Fin (n + 1)) ↦ (simplexInnerScale x) i)
  simp only [simplexInnerScale_weights]
  change Continuous (fun x : _root_.stdSimplex ℝ (Fin (n + 1)) ↦
    (1 / 4 : ℝ) * (1 / (n + 1)) + (3 / 4 : ℝ) * x.val i)
  exact continuous_const.add
    (continuous_const.mul ((continuous_apply i).comp continuous_subtype_val))

/-- Shrinking inserts a positive barycentric contribution in every coordinate. -/
theorem simplexInnerScale_mem_interior {n : ℕ}
    (x : _root_.stdSimplex ℝ (Fin (n + 1))) : simplexInnerScale x ∈ simplexInterior n := by
  intro i
  rw [simplexInnerScale_weights]
  have hpos : 0 < (1 / 4 : ℝ) * (1 / (n + 1)) := by positivity
  exact add_pos_of_pos_of_nonneg hpos (mul_nonneg (by norm_num) (stdSimplex.zero_le x i))

/-- Individual radial coordinate defects scale by `3/4`. -/
theorem simplexInnerScale_coordinateDefect {n : ℕ}
    (x : _root_.stdSimplex ℝ (Fin (n + 1))) (i : Fin (n + 1)) :
    1 - (n + 1 : ℝ) * (simplexInnerScale x) i =
      (3 / 4 : ℝ) * (1 - (n + 1 : ℝ) * x i) := by
  rw [simplexInnerScale_weights]
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- The maximal barycentric defect scales by `3/4`. -/
theorem simplexBoundaryDefect_innerScale {n : ℕ}
    (x : _root_.stdSimplex ℝ (Fin (n + 1))) :
    simplexBoundaryDefect (simplexInnerScale x) = (3 / 4 : ℝ) * simplexBoundaryDefect x := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _
    rw [simplexInnerScale_coordinateDefect]
    exact mul_le_mul_of_nonneg_left (le_simplexBoundaryDefect x i) (by norm_num)
  · obtain ⟨i, hi⟩ := exists_simplexBoundaryDefect_eq x
    calc
      (3 / 4 : ℝ) * simplexBoundaryDefect x =
          1 - (n + 1 : ℝ) * (simplexInnerScale x) i := by
            rw [simplexInnerScale_coordinateDefect, hi]
      _ ≤ simplexBoundaryDefect (simplexInnerScale x) :=
        le_simplexBoundaryDefect (simplexInnerScale x) i

/-- The overlap of the two genuine open simplex charts. -/
def simplexAnnulus (n : ℕ) : Set (_root_.stdSimplex ℝ (Fin (n + 1))) :=
  simplexBoundaryCollar n ∩ simplexInterior n

theorem isOpen_simplexAnnulus (n : ℕ) : IsOpen (simplexAnnulus n) :=
  (isOpen_simplexBoundaryCollar n).inter (isOpen_simplexInterior n)

/-- The shrunken boundary sits inside the open overlap. -/
theorem simplexInnerScale_boundary_mem_annulus {n : ℕ} (x : boundary n) :
    simplexInnerScale x.1 ∈ simplexAnnulus n := by
  refine ⟨?_, simplexInnerScale_mem_interior x.1⟩
  change (1 : ℝ) / 2 < simplexBoundaryDefect (simplexInnerScale x.1)
  rw [simplexBoundaryDefect_innerScale, (simplexBoundaryDefect_eq_one_iff x.1).mpr x.2]
  norm_num

/-- A coordinate attaining the maximal defect becomes zero after radial
projection from the collar to the boundary. -/
theorem simplexBoundaryRetractPoint_one_weights_zero {n : ℕ}
    (x : simplexBoundaryCollar n) (i : Fin (n + 1))
    (hi : simplexBoundaryDefect x.1 = 1 - (n + 1 : ℝ) * x.1 i) :
    (simplexBoundaryRetractPoint (x.1, 1)) i = 0 := by
  have hx : (1 : ℝ) / 2 < simplexBoundaryDefect x.1 := x.2
  have hs : simplexBoundaryScale (x.1, 1) = simplexBoundaryDefect x.1 := by
    unfold simplexBoundaryScale
    apply max_eq_right
    change 1 - (1 : ℝ) / 2 ≤ simplexBoundaryDefect x.1
    linarith
  rw [simplexBoundaryRetractPoint_weights]
  unfold simplexBoundaryRetractWeight
  rw [hs, hi]
  have hnum : (n + 1 : ℝ) * x.1 i +
      (1 - (n + 1 : ℝ) * x.1 i) - 1 = 0 := by ring
  rw [hnum, zero_div]

/-- A point of the open overlap joins the shrunken boundary along its own
radial line, and the entire segment stays in the open overlap. -/
theorem simplexAnnulus_joinedIn_innerBoundary {n : ℕ} (x : simplexAnnulus n) :
    ∃ y : boundary n,
      JoinedIn (simplexAnnulus n) x.1 (simplexInnerScale y.1) := by
  let xc : simplexBoundaryCollar n := ⟨x.1, x.2.1⟩
  let y : boundary n := ⟨simplexBoundaryRetractPoint (x.1, 1),
    simplexBoundaryRetractPoint_one_mem_boundary xc⟩
  obtain ⟨i, hi⟩ := exists_simplexBoundaryDefect_eq x.1
  have hy0 : y.1 i = 0 := simplexBoundaryRetractPoint_one_weights_zero xc i hi
  have hiy : 1 - (n + 1 : ℝ) * (simplexInnerScale y.1) i = 3 / 4 := by
    rw [simplexInnerScale_coordinateDefect, hy0]
    ring
  refine ⟨y, simplexSegment x.1 (simplexInnerScale y.1), fun t ↦ ⟨?_, ?_⟩⟩
  · change (1 : ℝ) / 2 < simplexBoundaryDefect (simplexSegment x.1 (simplexInnerScale y.1) t)
    apply lt_of_lt_of_le _ (le_simplexBoundaryDefect _ i)
    rw [simplexSegment_apply]
    have hlin : 1 - (n + 1 : ℝ) *
        ((1 - (t : ℝ)) * x.1 i + t * (simplexInnerScale y.1) i) =
        (1 - (t : ℝ)) * simplexBoundaryDefect x.1 + t * (3 / 4 : ℝ) := by
      calc
        _ = (1 - (t : ℝ)) * (1 - (n + 1 : ℝ) * x.1 i) +
            t * (1 - (n + 1 : ℝ) * (simplexInnerScale y.1) i) := by ring
        _ = _ := by rw [← hi, hiy]
    rw [hlin]
    have hx : (1 : ℝ) / 2 < simplexBoundaryDefect x.1 := x.2.1
    have ht0 := t.2.1
    have ht1 := t.2.2
    by_cases ht : (t : ℝ) = 0
    · simpa only [ht, sub_zero, one_mul, zero_mul, add_zero] using hx
    · have hpos : 0 < (t : ℝ) * (1 / 4 : ℝ) :=
        mul_pos (lt_of_le_of_ne ht0 (Ne.symm ht)) (by norm_num)
      have hnonneg : 0 ≤ (1 - (t : ℝ)) * (simplexBoundaryDefect x.1 - 1 / 2) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
  · exact simplexSegment_mem_interior x.2.2 (simplexInnerScale_mem_interior y.1) t

/-- The collar/interior overlap is path-connected in dimensions at least two. -/
theorem isPathConnected_simplexAnnulus {n : ℕ} (hn : 2 ≤ n) :
    IsPathConnected (simplexAnnulus n) := by
  have hs := (isPathConnected_simplexBoundary hn).image continuous_simplexInnerScale
  have hsub : simplexInnerScale '' boundary n ⊆ simplexAnnulus n := by
    rintro _ ⟨x, hx, rfl⟩
    exact simplexInnerScale_boundary_mem_annulus ⟨x, hx⟩
  obtain ⟨b, hb, hpaths⟩ := hs
  refine ⟨b, hsub hb, ?_⟩
  intro x hx
  obtain ⟨y, hy⟩ := simplexAnnulus_joinedIn_innerBoundary ⟨x, hx⟩
  exact ((hpaths ⟨y.1, y.2, rfl⟩).mono hsub).trans hy.symm

end stdSimplex

attribute [colib_tag "COL-0101",
  colib_ref "HatcherAT" "Chapter 0, proof of Proposition 0.16, page 15"
    "background"
    "Radial coordinates for the explicit annulus; not the stated disk-cylinder theorem"]
  stdSimplex.simplexInnerScale
  stdSimplex.simplexBoundaryDefect_innerScale
  stdSimplex.isOpen_simplexAnnulus
  stdSimplex.simplexAnnulus_joinedIn_innerBoundary
  stdSimplex.isPathConnected_simplexAnnulus
