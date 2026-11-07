/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.Topology.Realization.SimplexAnnulus

/-! Actual simplex charts and annulus regression tests. Interior results hold
in every dimension; boundary and annulus connectivity retain `2 ≤ n`. -/
@[expose] public noncomputable section
open scoped Topology unitInterval
namespace stdSimplex

example {n : ℕ} (x y : _root_.stdSimplex ℝ (Fin (n + 1))) (t : I) (i : Fin (n + 1)) :
    (simplexSegment x y t) i =
      (1 - (t : ℝ)) * x i + t * y i := simplexSegment_apply x y t i

example {n : ℕ} (hn : 2 ≤ n) : IsPathConnected (boundary n) :=
  isPathConnected_simplexBoundary hn

example (n : ℕ) : IsPathConnected (simplexInterior n) := isPathConnected_simplexInterior n

example {n : ℕ} (x : _root_.stdSimplex ℝ (Fin (n + 1))) :
    simplexBoundaryDefect (simplexInnerScale x) = (3 / 4 : ℝ) * simplexBoundaryDefect x :=
  simplexBoundaryDefect_innerScale x

example (n : ℕ) : simplexAnnulus n = simplexBoundaryCollar n ∩ simplexInterior n := rfl

example {n : ℕ} (x : boundary n) : simplexInnerScale x.1 ∈ simplexAnnulus n :=
  simplexInnerScale_boundary_mem_annulus x

example {n : ℕ} (x : simplexAnnulus n) : ∃ y : boundary n,
    JoinedIn (simplexAnnulus n) x.1 (simplexInnerScale y.1) :=
  simplexAnnulus_joinedIn_innerBoundary x

example {n : ℕ} (hn : 2 ≤ n) : IsPathConnected (simplexAnnulus n) :=
  isPathConnected_simplexAnnulus hn

example (n : ℕ) : IsSimplyConnected (simplexInterior n) :=
  isSimplyConnected_simplexInterior n

end stdSimplex



namespace stdSimplex

example (n : ℕ) (i : Fin (n + 1)) :
    (stdSimplex.barycenter : _root_.stdSimplex ℝ (Fin (n + 1))) i = (1 : ℝ) / (n + 1) := by
  change (stdSimplex.barycenter : _root_.stdSimplex ℝ (Fin (n + 1))).val i = _
  simp [stdSimplex.barycenter_apply, one_div]

example (n : ℕ) :
    (stdSimplex.barycenter : _root_.stdSimplex ℝ (Fin (n + 1))) ∈ simplexInterior n :=
  barycenter_mem_simplexInterior n

example {n : ℕ} (x y : _root_.stdSimplex ℝ (Fin (n + 1))) : simplexSegment x y 0 = x :=
  (simplexSegment x y).source

example {n : ℕ} (x y : _root_.stdSimplex ℝ (Fin (n + 1))) : simplexSegment x y 1 = y :=
  (simplexSegment x y).target

example {n : ℕ} {x y : _root_.stdSimplex ℝ (Fin (n + 1))}
    (hx : x ∈ simplexInterior n) (hy : y ∈ simplexInterior n) (t : I) :
    simplexSegment x y t ∈ simplexInterior n := simplexSegment_mem_interior hx hy t

example (n : ℕ) : simplexInterior n = (boundary n)ᶜ :=
  simplexInterior_eq_compl_boundary n

example : IsSimplyConnected (simplexInterior 0) := isSimplyConnected_simplexInterior 0

example : IsSimplyConnected (simplexInterior 1) := isSimplyConnected_simplexInterior 1

example {n : ℕ} (x : _root_.stdSimplex ℝ (Fin (n + 1))) (i : Fin (n + 1)) :
    (simplexInnerScale x) i =
      (1 / 4 : ℝ) * (1 / (n + 1)) + (3 / 4 : ℝ) * x i :=
  simplexInnerScale_weights x i

example {n : ℕ} (x : _root_.stdSimplex ℝ (Fin (n + 1))) :
    simplexInnerScale x ∈ simplexInterior n := simplexInnerScale_mem_interior x

example (n : ℕ) : IsOpen (simplexAnnulus n) := isOpen_simplexAnnulus n

example {n : ℕ} (x : simplexBoundaryCollar n) (i : Fin (n + 1))
    (hi : simplexBoundaryDefect x.1 = 1 - (n + 1 : ℝ) * x.1 i) :
    (simplexBoundaryRetractPoint (x.1, 1)) i = 0 :=
  simplexBoundaryRetractPoint_one_weights_zero x i hi

end stdSimplex
