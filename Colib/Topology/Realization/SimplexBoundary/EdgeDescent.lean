/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.SimplexBoundary.BoundaryEdges
public import Colib.Topology.Realization.SimplexBoundary.MidpointDescent

/-!
# Edge Descent

An exact original edge transport identity implies the midpoint overlap
identity, using the actual face homotopy between its two spokes and that edge.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set CategoryTheory Convexity.StdSimplex FundamentalGroupoid.OpenCover
universe u v
namespace Convexity.StdSimplex.Boundary
variable {n : ℕ}

/-- An exact original edge transport identity implies the midpoint overlap
identity, using the actual face homotopy between its two spokes and that edge. -/
theorem midpoint_potential_eq_of_edge {C : Type u} [Groupoid.{v} C]
    (F : FundamentalGroupoid (boundary (n + 2)) ⥤ C) (b : C)
    (β : ∀ i, F.obj (FundamentalGroupoid.mk (vertex i)) ≅ b) (i j : Fin (n + 3))
    (he : F.map (Path.Homotopic.Quotient.mk (boundaryEdge i j)) ≫ (β j).hom = (β i).hom) :
    (starPotentialIso F b β i).app
        (FundamentalGroupoid.mk ⟨edgeMidpoint i j, (edgeMidpoint_mem i j).1⟩) =
    (starPotentialIso F b β j).app
        (FundamentalGroupoid.mk ⟨edgeMidpoint i j, (edgeMidpoint_mem i j).2⟩) := by
  apply Iso.ext
  change (starPotentialIso F b β i).hom.app
      (FundamentalGroupoid.mk ⟨edgeMidpoint i j, (edgeMidpoint_mem i j).1⟩) =
    (starPotentialIso F b β j).hom.app
      (FundamentalGroupoid.mk ⟨edgeMidpoint i j, (edgeMidpoint_mem i j).2⟩)
  rw [starPotentialIso_hom_app, starPotentialIso_hom_app]
  change F.map (Path.Homotopic.Quotient.mk (midpointSpokeLeft i j)) ≫ (β i).hom =
    F.map (Path.Homotopic.Quotient.mk (midpointSpokeRight i j)) ≫ (β j).hom
  have hq : Path.Homotopic.Quotient.mk
      ((midpointSpokeLeft i j).symm.trans (midpointSpokeRight i j)) =
      Path.Homotopic.Quotient.mk (boundaryEdge i j) :=
    _root_.Quotient.sound ⟨midpointSpokesHomotopy i j⟩
  have hmap := congrArg
    (fun f : FundamentalGroupoid.mk (vertex i) ⟶ FundamentalGroupoid.mk (vertex j) => F.map f) hq
  change F.map (Groupoid.inv (Path.Homotopic.Quotient.mk (midpointSpokeLeft i j)) ≫
    Path.Homotopic.Quotient.mk (midpointSpokeRight i j)) = _ at hmap
  rw [Groupoid.inv_eq_inv] at hmap
  have hc : F.map (Path.Homotopic.Quotient.mk (midpointSpokeLeft i j)) ≫
      F.map (Path.Homotopic.Quotient.mk (boundaryEdge i j)) =
      F.map (Path.Homotopic.Quotient.mk (midpointSpokeRight i j)) := by
    rw [← hmap, F.map_comp, F.map_inv]
    simp
  rw [← he, ← Category.assoc, hc]

/-- Finite actual-edge potential equations construct a constant natural
isomorphism on the whole geometric simplex boundary. -/
def boundaryConstantIsoOfEdges {C : Type u} [Groupoid.{v} C]
    (F : FundamentalGroupoid (boundary (n + 2)) ⥤ C) (b : C)
    (β : ∀ i, F.obj (FundamentalGroupoid.mk (vertex i)) ≅ b)
    (he : ∀ i j,
      F.map (Path.Homotopic.Quotient.mk (boundaryEdge i j)) ≫ (β j).hom = (β i).hom) :
    F ≅ (Functor.const (FundamentalGroupoid (boundary (n + 2)))).obj b :=
  boundaryConstantIsoOfMidpoints F b β (fun i j => midpoint_potential_eq_of_edge F b β i j (he i j))

/-- Every actual boundary loop is killed under the explicit finite original-edge
potential equations. No hypothesis already states global loop vanishing. -/
theorem boundary_loop_eq_id_of_edges {C : Type u} [Groupoid.{v} C]
    (F : FundamentalGroupoid (boundary (n + 2)) ⥤ C) (b : C)
    (β : ∀ i, F.obj (FundamentalGroupoid.mk (vertex i)) ≅ b)
    (he : ∀ i j,
      F.map (Path.Homotopic.Quotient.mk (boundaryEdge i j)) ≫ (β j).hom = (β i).hom)
    (x : boundary (n + 2)) (p : Path x x) :
    F.map (Path.Homotopic.Quotient.mk p) = 𝟙 (F.obj (FundamentalGroupoid.mk x)) :=
  boundary_loop_eq_id_of_midpoints F b β
    (fun i j => midpoint_potential_eq_of_edge F b β i j (he i j)) x p

end Convexity.StdSimplex.Boundary
