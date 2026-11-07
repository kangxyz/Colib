/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Homotopy.OpenCover.TransitionData

/-!
# Collar Overlap

The old-stage decoder pulled back along the actual collar retraction and
then restricted to the actual collar/interior overlap.
-/

@[expose] public section

noncomputable section
open Set CategoryTheory
universe u v w z
namespace FundamentalGroupoid.OpenCover
variable {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y]
variable {C : Type w} [Category.{z} C]

/-- The old-stage decoder pulled back along the actual collar retraction and
then restricted to the actual collar/interior overlap. -/
def collarOverlapFunctor (U V : Set X) (r : C(U, Y)) (F : FundamentalGroupoid Y ⥤ C) :
    FundamentalGroupoid ↥(U ∩ V) ⥤ C :=
  FundamentalGroupoid.map (r.comp ((ContinuousMap.inclusion (s := U ∩ V)
      Set.inter_subset_left))) ⋙ F

/-- The pullback acts on an actual overlap path by the actual retracted path. -/
theorem collarOverlapFunctor_path (U V : Set X) (r : C(U, Y))
    (F : FundamentalGroupoid Y ⥤ C) {x y : ↥(U ∩ V)} (p : Path x y) :
    (collarOverlapFunctor U V r F).map (Path.Homotopic.Quotient.mk p) =
      F.map (Path.Homotopic.Quotient.mk
        (p.map (r.continuous.comp ((ContinuousMap.inclusion (s := U ∩ V)
            Set.inter_subset_left)).continuous))) := rfl

/-- Conditional overlap extension data from the exact old-stage loop condition.
In dimension two this condition must be proved from the actual triangle
boundary relation; it is not supplied by connectedness of the overlap. -/
def collarOverlapConstantIso (U V : Set X) (r : C(U, Y))
    (F : FundamentalGroupoid Y ⥤ C) (b : ↥(U ∩ V))
    (α : ∀ x : ↥(U ∩ V), Path x b)
    (hloop : ∀ p : Path b b,
      F.map (Path.Homotopic.Quotient.mk
        (p.map (r.continuous.comp ((ContinuousMap.inclusion (s := U ∩ V)
            Set.inter_subset_left)).continuous))) =
      𝟙 (F.obj (FundamentalGroupoid.mk (r ((ContinuousMap.inclusion (s := U ∩ V)
          Set.inter_subset_left) b))))) :
    collarOverlapFunctor U V r F ≅
      (Functor.const (FundamentalGroupoid ↥(U ∩ V))).obj
        (F.obj (FundamentalGroupoid.mk (r ((ContinuousMap.inclusion (s := U ∩ V)
            Set.inter_subset_left) b)))) :=
  constantIsoOfActualLoops (collarOverlapFunctor U V r F) b α hloop

end FundamentalGroupoid.OpenCover
