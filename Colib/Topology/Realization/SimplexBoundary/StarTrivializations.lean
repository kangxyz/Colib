/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.SimplexBoundary.OverlapStars
public import Colib.Topology.Homotopy.OpenCover.LocalTrivializations
public import Colib.Topology.Homotopy.OpenCover.OverlapLoops

/-!
# Star Trivializations

The actual finite open star cover.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set CategoryTheory Convexity Convexity.StdSimplex FundamentalGroupoid.OpenCover
open scoped unitInterval
universe u v
namespace Convexity.StdSimplex.Boundary
variable {n : ℕ}

/-- The actual finite open star cover. -/
theorem starCover : CoverData (vertexStar (n := n)) where
  isOpen := isOpen_vertexStar
  covers := vertexStars_cover

/-- The actual contraction spoke, with both endpoints in the same star. -/
def starSpoke (i : Fin (n + 3)) (x : vertexStar i) : Path x ⟨vertex i, vertex_mem i⟩ where
  toFun t := vertexStarContraction i (t, x)
  continuous_toFun := (vertexStarContraction i).continuous.comp
    (continuous_id.prodMk continuous_const)
  source' := (vertexStarContraction i).map_zero_left x
  target' := (vertexStarContraction i).map_one_left x

/-- The original geometric formula of each contraction spoke. -/
theorem starSpoke_val (i : Fin (n + 3)) (x : vertexStar i) (t : I) :
    (starSpoke i x t).val.val = simplexSegment x.val.val (vertex i).val t := rfl

/-- A functor on the actual simplex boundary is trivialized on each actual
open star using its specified straight spokes and proved contractibility. -/
def starTrivialization {C : Type u} [Category.{v} C]
    (F : FundamentalGroupoid (boundary (n + 2)) ⥤ C) (i : Fin (n + 3)) :
    FundamentalGroupoid.map ((ContinuousMap.subtypeVal (vertexStar i))) ⋙ F ≅
      (Functor.const (FundamentalGroupoid (vertexStar i))).obj
        (F.obj (FundamentalGroupoid.mk (vertex i))) := by
  let : ContractibleSpace (vertexStar i) := contractible_vertexStar i
  exact constantIsoOfActualLoops (FundamentalGroupoid.map ((ContinuousMap.subtypeVal (vertexStar
      i))) ⋙ F)
    ⟨vertex i, vertex_mem i⟩ (starSpoke i)
    (map_actual_loop_eq_id _ _)

/-- Choose specified original vertex potentials to a common target object.
This is still a local natural isomorphism, not assumed global loop killing. -/
def starPotentialIso {C : Type u} [Category.{v} C]
    (F : FundamentalGroupoid (boundary (n + 2)) ⥤ C) (b : C)
    (β : ∀ i, F.obj (FundamentalGroupoid.mk (vertex i)) ≅ b) (i : Fin (n + 3)) :
    FundamentalGroupoid.map ((ContinuousMap.subtypeVal (vertexStar i))) ⋙ F ≅
      (Functor.const (FundamentalGroupoid (vertexStar i))).obj b :=
  starTrivialization F i ≪≫ (Functor.const (FundamentalGroupoid (vertexStar i))).mapIso (β i)

/-- Exact component formula: the actual spoke class followed by the specified
original vertex potential. -/
theorem starPotentialIso_hom_app {C : Type u} [Category.{v} C]
    (F : FundamentalGroupoid (boundary (n + 2)) ⥤ C) (b : C)
    (β : ∀ i, F.obj (FundamentalGroupoid.mk (vertex i)) ≅ b)
    (i : Fin (n + 3)) (x : vertexStar i) :
    (starPotentialIso F b β i).hom.app (FundamentalGroupoid.mk x) =
      F.map (Path.Homotopic.Quotient.mk
        ((starSpoke i x).map ((ContinuousMap.subtypeVal (vertexStar i))).continuous)) ≫ (β
            i).hom := rfl

end Convexity.StdSimplex.Boundary
