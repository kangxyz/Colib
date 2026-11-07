/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.ClassifyingSpace.NerveCompletion.GraphHomotopyReflection

/-!
# Original Arrow Lift

Every original nerve one-simplex has a path in the actual original graph
stage whose included points are EXACTLY its original realized-arrow path.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set CategoryTheory stdSimplex FundamentalGroupoid.OpenCover SSet
open stdSimplex.Boundary
open scoped Simplicial
universe u v
namespace CategoryTheory.NerveCompletion
open FundamentalGroupoid.OpenCover
open TopCat.SimplexAttachment
open stdSimplex.Boundary
open FundamentalGroupoid.SequentialColimit
attribute [local instance] Localization.groupoid

/-- Every original nerve one-simplex has a path in the actual original graph
stage whose included points are EXACTLY its original realized-arrow path. -/
theorem simplex_graph_path (C : Type u) [Category.{v} C] (s : (nerve C) _⦋1⦌) :
    ∃ p : Path (graphVertex C (s.obj 0)) (graphVertex C (s.obj 1)),
      ∀ t, NerveGraphData.inclusion C (p t) = classifyingSpacePath (s.map' 0 1) t := by
  classical
  by_cases hs : s ∈ (nerve C).nonDegenerate 1
  · let a := oneCellOfNondegenerate C s hs
    have h0 := oldGraphPoint_eq_original C (NerveGraphData.attaching C (a, boundaryZero))
      (a.simplex.obj 0) (NerveGraphData.oldObject_source C a)
    have h1 := oldGraphPoint_eq_original C (NerveGraphData.attaching C (a, boundaryOne))
      (a.simplex.obj 1) (NerveGraphData.oldObject_target C a)
    refine ⟨(nerveGraphEdgePath C a).cast h0.symm h1.symm, ?_⟩
    intro t
    exact NerveGraphData.characteristic_path C a t
  · obtain ⟨c, rfl⟩ := degenerate_one_eq_identity C s hs
    refine ⟨Path.refl (graphVertex C c), ?_⟩
    intro t
    change NerveGraphData.inclusion C (graphVertex C c) = classifyingSpacePath (𝟙 c) t
    rw [classifyingSpacePath_id]
    exact graphVertex_inclusion C c

/-- The previous actual graph lift applies to every original categorical arrow,
including identities, without any nondegeneracy assumption. -/
theorem originalArrow_graph_path (C : Type u) [Category.{v} C] {c d : C} (f : c ⟶ d) :
    ∃ p : Path (graphVertex C c) (graphVertex C d),
      ∀ t, NerveGraphData.inclusion C (p t) = classifyingSpacePath f t :=
  simplex_graph_path C (ComposableArrows.mk₁ f)

/-- The exact original ambient object identification, not a chosen path. -/
def graphAmbientIso (C : Type u) [Category.{v} C] (c : C) :
    (FundamentalGroupoid.map (NerveGraphData.inclusion C)).obj
        (FundamentalGroupoid.mk (graphVertex C c)) ≅
      FundamentalGroupoid.mk (classifyingSpacePoint c) :=
  eqToIso (congrArg FundamentalGroupoid.mk (graphVertex_inclusion C c))

/-- Exact ambient class of an actual graph lift, with both original vertex transports. -/
theorem originalArrow_ambient_trace (C : Type u) [Category.{v} C] {c d : C} (f : c ⟶ d)
    (p : Path (graphVertex C c) (graphVertex C d))
    (hp : ∀ t, NerveGraphData.inclusion C (p t) = classifyingSpacePath f t) :
    (FundamentalGroupoid.map (NerveGraphData.inclusion C)).map (Path.Homotopic.Quotient.mk p) =
      (graphAmbientIso C c).hom ≫
        (classifyingFundamentalGroupoidFunctor C).map f ≫ (graphAmbientIso C d).inv := by
  have he : p.map (NerveGraphData.inclusion C).continuous =
      (classifyingSpacePath f).cast (graphVertex_inclusion C c) (graphVertex_inclusion C d) := by
    apply Path.ext
    funext t
    exact hp t
  change Path.Homotopic.Quotient.mk (p.map (NerveGraphData.inclusion C).continuous) = _
  rw [he, Path.Homotopic.Quotient.mk_cast, ← FundamentalGroupoid.conj_eqToHom]
  rfl

end CategoryTheory.NerveCompletion
