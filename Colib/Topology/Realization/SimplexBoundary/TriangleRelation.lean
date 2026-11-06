/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Realization.SimplexBoundary.EdgeDescent
public import Colib.Topology.Realization.SimplexBoundary.EdgeMap

/-!
# Triangle Relation

A single original triangle relation implies all nine finite edge-potential
equations, using only genuine reversal and constant-edge identities.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Convexity Convexity.StdSimplex FundamentalGroupoid.OpenCover
universe u v
namespace Convexity.StdSimplex.Boundary

/-- A single original triangle relation implies all nine finite edge-potential
equations, using only genuine reversal and constant-edge identities. -/
theorem triangle_edge_coherence {C : Type u} [Groupoid.{v} C]
    (F : FundamentalGroupoid (simplexBoundary 2) ⥤ C)
    (h : edgeMap F 0 1 ≫ edgeMap F 1 2 = edgeMap F 0 2) (i j : Fin 3) :
    edgeMap F 0 i ≫ edgeMap F i j = edgeMap F 0 j := by
  fin_cases i <;> fin_cases j
  · change edgeMap F 0 0 ≫ edgeMap F 0 0 = edgeMap F 0 0
    simp only [edgeMap_self, Category.id_comp]
  · change edgeMap F 0 0 ≫ edgeMap F 0 1 = edgeMap F 0 1
    rw [edgeMap_self, Category.id_comp]
  · change edgeMap F 0 0 ≫ edgeMap F 0 2 = edgeMap F 0 2
    rw [edgeMap_self, Category.id_comp]
  · change edgeMap F 0 1 ≫ edgeMap F 1 0 = edgeMap F 0 0
    rw [edgeMap_reverse F 0 1, edgeMap_self]
    simp
  · change edgeMap F 0 1 ≫ edgeMap F 1 1 = edgeMap F 0 1
    rw [edgeMap_self, Category.comp_id]
  · exact h
  · change edgeMap F 0 2 ≫ edgeMap F 2 0 = edgeMap F 0 0
    rw [edgeMap_reverse F 0 2, edgeMap_self]
    simp
  · change edgeMap F 0 2 ≫ edgeMap F 2 1 = edgeMap F 0 1
    rw [edgeMap_reverse F 1 2, ← h]
    simp [Category.assoc]
  · change edgeMap F 0 2 ≫ edgeMap F 2 2 = edgeMap F 0 2
    rw [edgeMap_self, Category.comp_id]

/-- The chosen potentials satisfy the exact original edge equations. -/
theorem trianglePotential_edge {C : Type u} [Groupoid.{v} C]
    (F : FundamentalGroupoid (simplexBoundary 2) ⥤ C)
    (h : edgeMap F 0 1 ≫ edgeMap F 1 2 = edgeMap F 0 2) (i j : Fin 3) :
    edgeMap F i j ≫ (vertexPotential F j).hom = (vertexPotential F i).hom := by
  change edgeMap F i j ≫ inv (edgeMap F 0 j) = inv (edgeMap F 0 i)
  apply (cancel_epi (edgeMap F 0 i)).mp
  rw [← Category.assoc, triangle_edge_coherence F h]
  simp

/-- The actual triangle relation constructs a constant natural isomorphism on
the entire actual boundary. Every overlap-path check is proved in the preceding
leaves, rather than assumed by a global decoder hypothesis. -/
def boundaryConstantIsoOfTriangle {C : Type u} [Groupoid.{v} C]
    (F : FundamentalGroupoid (simplexBoundary 2) ⥤ C)
    (h : edgeMap F 0 1 ≫ edgeMap F 1 2 = edgeMap F 0 2) :
    F ≅ (Functor.const (FundamentalGroupoid (simplexBoundary 2))).obj
      (F.obj (FundamentalGroupoid.mk (vertex 0))) :=
  boundaryConstantIsoOfEdges F _ (vertexPotential F) (trianglePotential_edge F h)

/-- The single explicit original triangle relation kills every actual boundary
loop. Instantiating the relation for the nerve attaching map remains separate. -/
theorem boundary_loop_eq_id_of_triangle {C : Type u} [Groupoid.{v} C]
    (F : FundamentalGroupoid (simplexBoundary 2) ⥤ C)
    (h : edgeMap F 0 1 ≫ edgeMap F 1 2 = edgeMap F 0 2)
    (x : simplexBoundary 2) (p : Path x x) :
    F.map (Path.Homotopic.Quotient.mk p) = 𝟙 (F.obj (FundamentalGroupoid.mk x)) :=
  boundary_loop_eq_id_of_edges F _ (vertexPotential F) (trianglePotential_edge F h) x p

end Convexity.StdSimplex.Boundary
