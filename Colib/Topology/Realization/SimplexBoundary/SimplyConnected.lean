/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Realization.SimplexBoundary.FilledTriangles
public import Colib.Topology.Realization.SimplexBoundary.EdgeDescent
public import Colib.Topology.Realization.SimplexBoundary.EdgeMap

/-!
# Simply Connected

Potential equations follow from the actual filled triangular face.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set CategoryTheory stdSimplex FundamentalGroupoid.OpenCover
universe u v
namespace stdSimplex.Boundary
variable {n : ℕ}

/-- Potential equations follow from the actual filled triangular face. -/
theorem vertexPotential_edge {C : Type u} [Groupoid.{v} C]
    (F : FundamentalGroupoid (boundary (n + 3)) ⥤ C) (i j : Fin (n + 4)) :
    F.map (Path.Homotopic.Quotient.mk (boundaryEdge i j)) ≫
      (vertexPotential F j).hom = (vertexPotential F i).hom := by
  change edgeMap F i j ≫ inv (edgeMap F 0 j) = inv (edgeMap F 0 i)
  apply (cancel_epi (edgeMap F 0 i)).mp
  rw [← Category.assoc]
  have h : edgeMap F 0 i ≫ edgeMap F i j = edgeMap F 0 j :=
    boundaryEdge_triangle F 0 i j
  rw [h]
  simp

/-- Every groupoid-valued functor on an actual simplex boundary of dimension
at least three is naturally constant. All overlap path compatibility is proved. -/
def boundaryConstantIso {C : Type u} [Groupoid.{v} C]
    (F : FundamentalGroupoid (boundary (n + 3)) ⥤ C) :
    F ≅ (Functor.const (FundamentalGroupoid (boundary (n + 3)))).obj
      (F.obj (FundamentalGroupoid.mk (vertex 0))) :=
  boundaryConstantIsoOfEdges F _ (vertexPotential F) (vertexPotential_edge F)

/-- Every actual higher-boundary loop is killed, without a loop-killing premise. -/
theorem boundary_loop_eq_id {C : Type u} [Groupoid.{v} C]
    (F : FundamentalGroupoid (boundary (n + 3)) ⥤ C)
    (x : boundary (n + 3)) (p : Path x x) :
    F.map (Path.Homotopic.Quotient.mk p) = 𝟙 (F.obj (FundamentalGroupoid.mk x)) :=
  boundary_loop_eq_id_of_edges F _ (vertexPotential F) (vertexPotential_edge F) x p

end stdSimplex.Boundary

namespace stdSimplex

/-- The actual finite simplex boundary is simply connected in every dimension at least three. -/
theorem isSimplyConnected_simplexBoundary {n : ℕ} (hn : 3 ≤ n) :
    IsSimplyConnected (boundary n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 3 + m = m + 3 by omega]
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨isPathConnected_iff_pathConnectedSpace.mp
    (isPathConnected_simplexBoundary (by omega : 2 ≤ m + 3)), ?_⟩
  intro x p
  exact Path.Homotopic.Quotient.eq.mp
    (Boundary.boundary_loop_eq_id (𝟭 (FundamentalGroupoid (boundary (m + 3)))) x p)

end stdSimplex
