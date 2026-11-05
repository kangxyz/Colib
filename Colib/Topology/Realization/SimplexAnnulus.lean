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
open Convexity Set
open scoped Topology unitInterval BigOperators

namespace Convexity.StdSimplex

/-- Shrink a simplex toward its barycenter by the fixed radial factor `3/4`. -/
def simplexInnerScale {n : ℕ} (x : StdSimplex ℝ (Fin (n + 1))) :
    StdSimplex ℝ (Fin (n + 1)) :=
  convexCombPair (R := ℝ) (1 / 4) (3 / 4) (by norm_num) (by norm_num) (by norm_num)
    (simplexInteriorCenter n) x

@[simp] theorem simplexInnerScale_weights {n : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (i : Fin (n + 1)) :
    (simplexInnerScale x).weights i =
      (1 / 4 : ℝ) * (1 / (n + 1)) + (3 / 4 : ℝ) * x.weights i := by
  simp [simplexInnerScale, StdSimplex.weights_convexCombPair]

@[fun_prop] theorem continuous_simplexInnerScale {n : ℕ} :
    Continuous (simplexInnerScale (n := n)) := by
  rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).continuous_iff]
  apply continuous_pi
  intro i
  change Continuous (fun x : StdSimplex ℝ (Fin (n + 1)) ↦ (simplexInnerScale x).weights i)
  simp only [simplexInnerScale_weights]
  fun_prop

/-- Shrinking inserts a positive barycentric contribution in every coordinate. -/
theorem simplexInnerScale_mem_interior {n : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) : simplexInnerScale x ∈ simplexInterior n := by
  intro i
  rw [simplexInnerScale_weights]
  have hpos : 0 < (1 / 4 : ℝ) * (1 / (n + 1)) := by positivity
  exact add_pos_of_pos_of_nonneg hpos (mul_nonneg (by norm_num) (x.weights_nonneg i))

/-- Individual radial coordinate defects scale by `3/4`. -/
theorem simplexInnerScale_coordinateDefect {n : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) (i : Fin (n + 1)) :
    1 - (n + 1 : ℝ) * (simplexInnerScale x).weights i =
      (3 / 4 : ℝ) * (1 - (n + 1 : ℝ) * x.weights i) := by
  rw [simplexInnerScale_weights]
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- The maximal barycentric defect scales by `3/4`. -/
theorem simplexBoundaryDefect_innerScale {n : ℕ}
    (x : StdSimplex ℝ (Fin (n + 1))) :
    simplexBoundaryDefect (simplexInnerScale x) = (3 / 4 : ℝ) * simplexBoundaryDefect x := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _
    rw [simplexInnerScale_coordinateDefect]
    exact mul_le_mul_of_nonneg_left (le_simplexBoundaryDefect x i) (by norm_num)
  · obtain ⟨i, hi⟩ := exists_simplexBoundaryDefect_eq x
    calc
      (3 / 4 : ℝ) * simplexBoundaryDefect x =
          1 - (n + 1 : ℝ) * (simplexInnerScale x).weights i := by
            rw [simplexInnerScale_coordinateDefect, hi]
      _ ≤ simplexBoundaryDefect (simplexInnerScale x) :=
        le_simplexBoundaryDefect (simplexInnerScale x) i

/-- The overlap of the two genuine open simplex charts. -/
def simplexAnnulus (n : ℕ) : Set (StdSimplex ℝ (Fin (n + 1))) :=
  simplexBoundaryCollar n ∩ simplexInterior n

theorem isOpen_simplexAnnulus (n : ℕ) : IsOpen (simplexAnnulus n) :=
  (isOpen_simplexBoundaryCollar n).inter (isOpen_simplexInterior n)

/-- The shrunken boundary sits inside the open overlap. -/
theorem simplexInnerScale_boundary_mem_annulus {n : ℕ} (x : simplexBoundary n) :
    simplexInnerScale x.1 ∈ simplexAnnulus n := by
  refine ⟨?_, simplexInnerScale_mem_interior x.1⟩
  change (1 : ℝ) / 2 < simplexBoundaryDefect (simplexInnerScale x.1)
  rw [simplexBoundaryDefect_innerScale, (simplexBoundaryDefect_eq_one_iff x.1).mpr x.2]
  norm_num

/-- A coordinate attaining the maximal defect becomes zero after radial
projection from the collar to the boundary. -/
theorem simplexBoundaryRetractPoint_one_weights_zero {n : ℕ}
    (x : simplexBoundaryCollar n) (i : Fin (n + 1))
    (hi : simplexBoundaryDefect x.1 = 1 - (n + 1 : ℝ) * x.1.weights i) :
    (simplexBoundaryRetractPoint (x.1, 1)).weights i = 0 := by
  have hx : (1 : ℝ) / 2 < simplexBoundaryDefect x.1 := x.2
  have hs : simplexBoundaryScale (x.1, 1) = simplexBoundaryDefect x.1 := by
    unfold simplexBoundaryScale
    apply max_eq_right
    change 1 - (1 : ℝ) / 2 ≤ simplexBoundaryDefect x.1
    linarith
  rw [simplexBoundaryRetractPoint_weights]
  unfold simplexBoundaryRetractWeight
  rw [hs, hi]
  have hnum : (n + 1 : ℝ) * x.1.weights i +
      (1 - (n + 1 : ℝ) * x.1.weights i) - 1 = 0 := by ring
  rw [hnum, zero_div]

/-- A point of the open overlap joins the shrunken boundary along its own
radial line, and the entire segment stays in the open overlap. -/
theorem simplexAnnulus_joinedIn_innerBoundary {n : ℕ} (x : simplexAnnulus n) :
    ∃ y : simplexBoundary n,
      JoinedIn (simplexAnnulus n) x.1 (simplexInnerScale y.1) := by
  let xc : simplexBoundaryCollar n := ⟨x.1, x.2.1⟩
  let y : simplexBoundary n := ⟨simplexBoundaryRetractPoint (x.1, 1),
    simplexBoundaryRetractPoint_one_mem_boundary xc⟩
  obtain ⟨i, hi⟩ := exists_simplexBoundaryDefect_eq x.1
  have hy0 : y.1.weights i = 0 := simplexBoundaryRetractPoint_one_weights_zero xc i hi
  have hiy : 1 - (n + 1 : ℝ) * (simplexInnerScale y.1).weights i = 3 / 4 := by
    rw [simplexInnerScale_coordinateDefect, hy0]
    ring
  refine ⟨y, simplexSegment x.1 (simplexInnerScale y.1), fun t ↦ ⟨?_, ?_⟩⟩
  · change (1 : ℝ) / 2 < simplexBoundaryDefect (simplexSegment x.1 (simplexInnerScale y.1) t)
    apply lt_of_lt_of_le _ (le_simplexBoundaryDefect _ i)
    rw [simplexSegment_weights]
    have hlin : 1 - (n + 1 : ℝ) *
        ((1 - (t : ℝ)) * x.1.weights i + t * (simplexInnerScale y.1).weights i) =
        (1 - (t : ℝ)) * simplexBoundaryDefect x.1 + t * (3 / 4 : ℝ) := by
      calc
        _ = (1 - (t : ℝ)) * (1 - (n + 1 : ℝ) * x.1.weights i) +
            t * (1 - (n + 1 : ℝ) * (simplexInnerScale y.1).weights i) := by ring
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
  have hsub : simplexInnerScale '' simplexBoundary n ⊆ simplexAnnulus n := by
    rintro _ ⟨x, hx, rfl⟩
    exact simplexInnerScale_boundary_mem_annulus ⟨x, hx⟩
  obtain ⟨b, hb, hpaths⟩ := hs
  refine ⟨b, hsub hb, ?_⟩
  intro x hx
  obtain ⟨y, hy⟩ := simplexAnnulus_joinedIn_innerBoundary ⟨x, hx⟩
  exact ((hpaths ⟨y.1, y.2, rfl⟩).mono hsub).trans hy.symm

end Convexity.StdSimplex

attribute [colib_tag "COL-0101",
  colib_ref "HatcherAT" "Chapter 0, proof of Proposition 0.16, page 15"
    "background"
    "Radial coordinates for the explicit annulus; not the stated disk-cylinder theorem"]
  Convexity.StdSimplex.simplexInnerScale
  Convexity.StdSimplex.simplexBoundaryDefect_innerScale
  Convexity.StdSimplex.isOpen_simplexAnnulus
  Convexity.StdSimplex.simplexAnnulus_joinedIn_innerBoundary
  Convexity.StdSimplex.isPathConnected_simplexAnnulus
