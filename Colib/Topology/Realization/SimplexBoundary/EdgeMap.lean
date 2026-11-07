/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Realization.SimplexBoundary.BoundaryEdges

/-!
# Edge Map

The repeated-vertex geometric edge is literally the constant path.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Convexity Convexity.StdSimplex
universe u v
namespace Convexity.StdSimplex.Boundary
variable {n : ℕ}

/-- The repeated-vertex geometric edge is literally the constant path. -/
theorem boundaryEdge_self (i : Fin (n + 3)) : boundaryEdge i i = Path.refl (vertex i) := by
  apply Path.ext
  funext t
  apply Subtype.ext
  apply StdSimplex.ext
  ext k
  change (simplexSegment (vertex i).val (vertex i).val t).weights k = (vertex i).val.weights k
  rw [simplexSegment_apply]
  ring

/-- Reversing an actual edge is literally the oppositely oriented edge. -/
theorem boundaryEdge_symm (i j : Fin (n + 3)) : (boundaryEdge i j).symm = boundaryEdge j i := by
  apply Path.ext
  funext t
  apply Subtype.ext
  apply StdSimplex.ext
  ext k
  change (simplexSegment (vertex i).val (vertex j).val (unitInterval.symm t)).weights k =
    (simplexSegment (vertex j).val (vertex i).val t).weights k
  rw [simplexSegment_apply, simplexSegment_apply]
  simp only [unitInterval.coe_symm_eq]
  ring

/-- The image of the specified actual geometric edge. -/
def edgeMap {C : Type u} [Groupoid.{v} C]
    (F : FundamentalGroupoid (boundary (n + 2)) ⥤ C) (i j : Fin (n + 3)) :
    F.obj (FundamentalGroupoid.mk (vertex i)) ⟶ F.obj (FundamentalGroupoid.mk (vertex j)) :=
  F.map (Path.Homotopic.Quotient.mk (boundaryEdge i j))

@[simp]
theorem edgeMap_self {C : Type u} [Groupoid.{v} C]
    (F : FundamentalGroupoid (boundary (n + 2)) ⥤ C) (i : Fin (n + 3)) :
    edgeMap F i i = 𝟙 (F.obj (FundamentalGroupoid.mk (vertex i))) := by
  unfold edgeMap
  rw [boundaryEdge_self]
  exact F.map_id _

theorem edgeMap_reverse {C : Type u} [Groupoid.{v} C]
    (F : FundamentalGroupoid (boundary (n + 2)) ⥤ C) (i j : Fin (n + 3)) :
    edgeMap F j i = inv (edgeMap F i j) := by
  unfold edgeMap
  rw [← boundaryEdge_symm i j]
  change F.map (Groupoid.inv (Path.Homotopic.Quotient.mk (boundaryEdge i j))) = _
  rw [Groupoid.inv_eq_inv, F.map_inv]

/-- Vertex potentials are the inverse classes of the actual edges from vertex zero. -/
def vertexPotential {C : Type u} [Groupoid.{v} C]
    (F : FundamentalGroupoid (boundary (n + 2)) ⥤ C) (i : Fin (n + 3)) :
    F.obj (FundamentalGroupoid.mk (vertex i)) ≅ F.obj (FundamentalGroupoid.mk (vertex 0)) :=
  (asIso (edgeMap F 0 i)).symm

end Convexity.StdSimplex.Boundary
