/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Realization.SimplexBoundary.BoundaryEdges

/-!
# Filled Triangles

Any three vertex indices omit a coordinate in a simplex of dimension at least three.
-/

@[expose] public section

noncomputable section
open Set CategoryTheory stdSimplex
open scoped unitInterval
universe u v
namespace stdSimplex.Boundary
variable {n : ℕ}

/-- Any three vertex indices omit a coordinate in a simplex of dimension at least three. -/
theorem exists_coordinate_outside (i j k : Fin (n + 4)) :
    ∃ l : Fin (n + 4), l ≠ i ∧ l ≠ j ∧ l ≠ k := by
  have hc : ({i, j, k} : Finset (Fin (n + 4))).card <
      (Finset.univ : Finset (Fin (n + 4))).card := by
    have h1 := Finset.card_insert_le i ({j, k} : Finset (Fin (n + 4)))
    have h2 := Finset.card_insert_le j ({k} : Finset (Fin (n + 4)))
    simp only [Finset.card_singleton, Finset.card_univ, Fintype.card_fin] at *
    omega
  obtain ⟨l, _, hl⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  exact ⟨l, by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hl⟩

/-- The actual triangle is filled inside one zero-coordinate boundary face.
Repeated indices are allowed and no boundary simple-connectedness is assumed. -/
def boundaryTriangleHomotopy (i j k : Fin (n + 4)) :
    ((boundaryEdge i j).trans (boundaryEdge j k)).Homotopy (boundaryEdge i k) := by
  let l := Classical.choose (exists_coordinate_outside i j k)
  have hl := Classical.choose_spec (exists_coordinate_outside i j k)
  have he (a b : Fin (n + 4)) (ha : l ≠ a) (hb : l ≠ b) :
      range (boundaryEdge a b) ⊆ {x | x.val l = 0} := by
    rintro _ ⟨t, rfl⟩
    change (simplexSegment (vertex a).val (vertex b).val t) l = 0
    rw [simplexSegment_apply]
    simp [vertex, stdSimplex.vertex_coe, Ne.symm ha, Ne.symm hb]
  have hp : range ((boundaryEdge i j).trans (boundaryEdge j k)) ⊆
      {x | x.val l = 0} := by
    rw [Path.trans_range]
    exact union_subset (he i j hl.1 hl.2.1) (he j k hl.2.1 hl.2.2)
  exact facePathHomotopy _ _ l (fun t => hp (mem_range_self t))
    (fun t => he i k hl.1 hl.2.2 (mem_range_self t))

/-- Every functor respects every actual filled triangular face, including repeated vertices. -/
theorem boundaryEdge_triangle {C : Type u} [Category.{v} C]
    (F : FundamentalGroupoid (boundary (n + 3)) ⥤ C) (i j k : Fin (n + 4)) :
    F.map (Path.Homotopic.Quotient.mk (boundaryEdge i j)) ≫
      F.map (Path.Homotopic.Quotient.mk (boundaryEdge j k)) =
      F.map (Path.Homotopic.Quotient.mk (boundaryEdge i k)) := by
  rw [← F.map_comp]
  apply congrArg F.map
  exact Path.Homotopic.Quotient.eq.mpr ⟨boundaryTriangleHomotopy i j k⟩

end stdSimplex.Boundary
