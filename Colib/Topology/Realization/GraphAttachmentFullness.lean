/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.GraphAttachmentPathGeneration

/-!
# Fullness from genuine graph edges

For a discrete family of geometric intervals attached to a discrete vertex
space, compatibility on the original vertices and whole edges suffices to
represent every continuous path by a morphism of the original groupoid.
The path may traverse infinitely many portions of edges before subdivision;
no edge-path approximation is assumed in the theorem.
-/
/-!
Adapted from `Quillen/Topology/Realization/EdgePathPresentation/GraphFullness.lean`
at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The actual supplied edges, spokes, vertex identifications and compatibility
hypothesis are retained, together with all space and groupoid universes.
The source hypotheses and actual path-class equations are retained.
-/
@[expose] public section

open Topology

noncomputable section
universe u v w
open CategoryTheory CategoryTheory.Limits _root_.stdSimplex Set
open scoped Topology unitInterval
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
namespace TopCat.GraphAttachment

variable (X : TopCat.{u}) [DiscreteTopology X] {V D Y : TopCat.{u}}
    [DiscreteTopology V]
    {f : TopCat.of (X × _root_.stdSimplex.boundary 1) ⟶ V}
    {g : TopCat.of (X × _root_.stdSimplex ℝ (Fin 2)) ⟶ D} {j : V ⟶ D}
    (sq : IsPushout (parameterizedSimplexBoundaryInclusion X 1) f g j)
    (h : C(D, Y)) {A : Type v} [Groupoid.{w} A]
    (F : A ⥤ FundamentalGroupoid Y) (vertex : V → A)
    (ε : ∀ c : V, F.obj (vertex c) ≅ FundamentalGroupoid.mk (h (j c)))
    (edge : ∀ a : X, vertex (f (a, boundaryZero)) ⟶ vertex (f (a, boundaryOne)))
    (hedge : ∀ a : X, spoke X sq h F vertex ε a (_root_.stdSimplex.vertex 1) =
      F.map (edge a) ≫ (vertexIso X sq h F vertex ε a boundaryOne).hom)

include hedge in
/-- If the actual graph inclusion is full on fundamental groupoids, original
vertex and whole-edge compatibility represents every ambient path class. -/
theorem map_surjective_of_ambient_full [(FundamentalGroupoid.map h).Full]
    (c d : V) :
    Function.Surjective (F.map : (vertex c ⟶ vertex d) → (F.obj (vertex c) ⟶
      F.obj (vertex d))) := by
  intro p
  obtain ⟨q, hq⟩ := (FundamentalGroupoid.map h).map_surjective
    (X := FundamentalGroupoid.mk (j c)) (Y := FundamentalGroupoid.mk (j d))
    ((ε c).inv ≫ p ≫ (ε d).hom)
  obtain ⟨q, rfl⟩ := Path.Homotopic.Quotient.mk_surjective q
  obtain ⟨r, hr⟩ := path_from_original_edges X sq h F vertex ε edge hedge q
  refine ⟨r, ?_⟩
  change (⟦q.map h.continuous⟧ : FundamentalGroupoid.mk (h (j c)) ⟶
    FundamentalGroupoid.mk (h (j d))) = (ε c).inv ≫ p ≫ (ε d).hom at hq
  rw [hr, hq]
  simp

end TopCat.GraphAttachment
