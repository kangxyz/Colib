/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.Topology.Realization.SimplexBoundaryCollar
public import Mathlib.Geometry.Convex.ConvexSpace.Barycenter
public import Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Data.Fin.Basic
public import Mathlib.Tactic.NormNum
public import Colib.Analysis.Convex.StdSimplex.PathHomotopy
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Connected boundary and simply connected simplex interior

Straight barycentric segments give explicit boundary paths in dimensions at
least two. The positive-coordinate interior is open, path-connected and simply
connected in every dimension. Shrinking the boundary and the collar/interior
overlap are treated separately in `SimplexAnnulus`.
-/
/-!
## Implementation provenance

Adapted from `Quillen/Topology/Realization/EdgePathPresentation/SimplexCharts.lean`
at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual barycentric
paths, barycenter, positive-coordinate interior and dimension hypotheses are retained.
Coordinate proofs use native finitely supported weights. Interior simple connectedness
retains its unrestricted dimension hypothesis.
-/
@[expose] public section


noncomputable section

open Convexity Set
open scoped Topology unitInterval BigOperators

namespace Convexity.StdSimplex

/-- The straight barycentric path between two points of a finite simplex. -/
def simplexSegment {n : ℕ} (x y : StdSimplex ℝ (Fin (n + 1))) : Path x y where
  toFun t := convexCombPair (R := ℝ) (unitInterval.symm t) t
    (unitInterval.nonneg _) (unitInterval.nonneg _) (by simp) x y
  continuous_toFun := StdSimplex.continuous_convexCombPair x y
  source' := by simp
  target' := by simp

@[simp] theorem simplexSegment_apply {n : ℕ}
    (x y : StdSimplex ℝ (Fin (n + 1))) (t : unitInterval) (i : Fin (n + 1)) :
    (simplexSegment x y t).weights i =
      (1 - (t : ℝ)) * x.weights i + t * y.weights i := by
  simp [simplexSegment, StdSimplex.weights_convexCombPair, unitInterval.coe_symm_eq]

/-- The native pushforward commutes with the straight coordinate segment. -/
theorem map_simplexSegment {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1))
    (x y : StdSimplex ℝ (Fin (m + 1))) (t : unitInterval) :
    StdSimplex.map f (simplexSegment x y t) =
      simplexSegment (StdSimplex.map f x) (StdSimplex.map f y) t := by
  exact (StdSimplex.isAffineMap_map ℝ f).map_convexCombPair _ _ _ x y

/-- Two points of one zero-coordinate face can be joined in that face. -/
theorem simplexBoundary_joinedIn_face {n : ℕ}
    (x y : StdSimplex ℝ (Fin (n + 1))) (i : Fin (n + 1))
    (hx : x.weights i = 0) (hy : y.weights i = 0) :
    JoinedIn (boundary n) x y := by
  refine ⟨simplexSegment x y, fun t ↦ ⟨i, ?_⟩⟩
  simp [hx, hy]

/-- In dimension at least two, the edge between any two vertices is contained
in the boundary: a third vertex supplies a zero coordinate along the edge. -/
theorem simplexBoundary_joinedIn_vertices {n : ℕ} (hn : 2 ≤ n)
    (i j : Fin (n + 1)) :
    JoinedIn (boundary n) (StdSimplex.single i) (StdSimplex.single j) := by
  obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega)
  exact simplexBoundary_joinedIn_face _ _ k
    (by simp [hki])
    (by simp [hkj])

/-- Every boundary point can be joined within the boundary to a vertex. -/
theorem simplexBoundary_joinedIn_vertex {n : ℕ} (hn : 2 ≤ n)
    (x : boundary n) :
    ∃ j : Fin (n + 1), JoinedIn (boundary n) x.1 (StdSimplex.single j) := by
  obtain ⟨i, hi⟩ := x.2
  obtain ⟨j, hji, _⟩ := Fin.exists_ne_and_ne_of_two_lt i i (by omega)
  exact ⟨j, simplexBoundary_joinedIn_face _ _ i hi
    (by simp [Ne.symm hji])⟩

/-- The boundary of a simplex of dimension at least two is path-connected. -/
theorem isPathConnected_simplexBoundary {n : ℕ} (hn : 2 ≤ n) :
    IsPathConnected (boundary n) := by
  have hzero := simplexBoundary_joinedIn_vertices hn (0 : Fin (n + 1)) 0
  refine ⟨StdSimplex.single 0, hzero.source_mem, ?_⟩
  intro x hx
  obtain ⟨j, hj⟩ := simplexBoundary_joinedIn_vertex hn ⟨x, hx⟩
  exact (simplexBoundary_joinedIn_vertices hn 0 j).trans hj.symm

/-- All coordinates of an interior point are strictly positive. -/
def simplexInterior (n : ℕ) : Set (StdSimplex ℝ (Fin (n + 1))) :=
  {x | ∀ i, 0 < x.weights i}

theorem simplexInterior_eq_compl_boundary (n : ℕ) :
    simplexInterior n = (boundary n)ᶜ := by
  ext x
  constructor
  · intro hx ⟨i, hi⟩
    exact (ne_of_gt (hx i)) hi
  · intro hx i
    apply lt_of_le_of_ne (StdSimplex.weights_nonneg (w := x) i)
    intro hi
    exact hx ⟨i, hi.symm⟩

theorem isOpen_simplexInterior (n : ℕ) : IsOpen (simplexInterior n) := by
  rw [simplexInterior_eq_compl_boundary]
  exact (isClosed_boundary n).isOpen_compl

/-- A convex combination of two positive real coordinates stays positive. -/
private theorem interval_weighted_pos (t : unitInterval) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) : 0 < (1 - (t : ℝ)) * a + t * b := by
  have ht0 := t.2.1
  have ht1 := t.2.2
  by_cases ht : (t : ℝ) = 0
  · simpa only [ht, sub_zero, one_mul, zero_mul, add_zero] using ha
  · have htb : 0 < (t : ℝ) * b := mul_pos (lt_of_le_of_ne ht0 (Ne.symm ht)) hb
    have hta : 0 ≤ (1 - (t : ℝ)) * a := mul_nonneg (by linarith) ha.le
    linarith

/-- Straight segments between interior points stay in the interior. -/
theorem simplexSegment_mem_interior {n : ℕ} {x y : StdSimplex ℝ (Fin (n + 1))}
    (hx : x ∈ simplexInterior n) (hy : y ∈ simplexInterior n) (t : unitInterval) :
    simplexSegment x y t ∈ simplexInterior n := by
  intro i
  rw [simplexSegment_apply]
  exact interval_weighted_pos t (hx i) (hy i)

/-- The native barycenter has strictly positive coordinates. -/
theorem barycenter_mem_simplexInterior (n : ℕ) :
    (Convexity.StdSimplex.barycenter : StdSimplex ℝ (Fin (n + 1))) ∈ simplexInterior n := by
  intro i
  change 0 < (StdSimplex.barycenter : StdSimplex ℝ (Fin (n + 1))).weights i
  rw [StdSimplex.weights_barycenter_apply]
  simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one]
  positivity

/-- The open geometric simplex is path-connected. -/
theorem isPathConnected_simplexInterior (n : ℕ) : IsPathConnected (simplexInterior n) :=
  ⟨Convexity.StdSimplex.barycenter, barycenter_mem_simplexInterior n,
    fun _ hy ↦ ⟨simplexSegment _ _,
      simplexSegment_mem_interior (barycenter_mem_simplexInterior n) hy⟩⟩

/-- The open geometric simplex is simply connected: linear interpolation of
paths stays in its strictly positive coordinate region. -/
theorem isSimplyConnected_simplexInterior (n : ℕ) : IsSimplyConnected (simplexInterior n) := by
  rw [IsSimplyConnected, simply_connected_iff_paths_homotopic']
  refine ⟨isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_simplexInterior n), ?_⟩
  intro x y p q
  let H := Convexity.StdSimplex.pathHomotopy
    (p.map continuous_subtype_val) (q.map continuous_subtype_val)
  have hH (z : unitInterval × unitInterval) : H z ∈ simplexInterior n := by
    intro i
    rw [Convexity.StdSimplex.pathHomotopy_apply]
    exact interval_weighted_pos z.1 ((p z.2).2 i) ((q z.2).2 i)
  exact ⟨{
    toFun := fun z ↦ ⟨H z, hH z⟩
    continuous_toFun := H.continuous.subtype_mk hH
    map_zero_left := fun t ↦ Subtype.ext (H.map_zero_left t)
    map_one_left := fun t ↦ Subtype.ext (H.map_one_left t)
    prop' := fun t z hz ↦ Subtype.ext (H.prop' t z hz) }⟩

end Convexity.StdSimplex

attribute [colib_tag "COL-0100",
  colib_ref "HatcherAT" "Section 1.1, Examples 1.1 and 1.4, pages 25 and 27"
    "adaptation"
    "Positive-coordinate simplex interior: straight paths and fixed-endpoint homotopies"]
  Convexity.StdSimplex.isPathConnected_simplexInterior
  Convexity.StdSimplex.isSimplyConnected_simplexInterior

attribute [colib_tag "COL-0100",
  colib_ref "HatcherAT" "Section 1.1, Example 1.1, page 25"
    "ingredient"
    "Face segments joined through vertices in dimensions at least two"]
  Convexity.StdSimplex.isPathConnected_simplexBoundary
