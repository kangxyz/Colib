/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.FunctorChain
public import Colib.Analysis.Convex.StdSimplex.PathHomotopy

/-!
# Actual two-parameter composition of realized natural transformations

The genuine two-simplex of a composable pair of natural transformations fills the region between
its composite edge and the concatenation of its two other edges. Convex interpolation inside that
simplex gives a jointly continuous comparison relative to both endpoints, for every source point.
This is a classifying-space statement; a coherent based prespectrum lift needs further checks.

## Implementation provenance

Adapted from `Quillen/CategoryTheory/TheoremB/CompositionHomotopy.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, chosen paths, and original
proof hypotheses are retained under native ownership.
-/
@[expose] public section

noncomputable section
open Topology SSet HomotopyGroup

open CategoryTheory
open scoped Topology unitInterval

universe u

namespace CategoryTheory.TheoremB

/-- The actual affine path along a specified edge of the triangle. -/
def triangleEdgePath (i j : Fin 3) :
    Path (Convexity.StdSimplex.single i : Convexity.StdSimplex ℝ (Fin 3))
      (Convexity.StdSimplex.single j) where
  toFun := triangleEdge i j
  continuous_toFun := continuous_triangleEdge i j
  source' := triangleEdge_zero i j
  target' := triangleEdge_one i j

/-- Convex interpolation between the original composite edge and the two other triangle edges. -/
def compositionTriangleHomotopy :
    (triangleEdgePath 0 2).Homotopy ((triangleEdgePath 0 1).trans (triangleEdgePath 1 2)) :=
  Convexity.StdSimplex.pathHomotopy _ _

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {F G H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H)

/-- The original composite-transformation track is endpoint-relatively homotopic to the
concatenation of the two original transformation tracks, continuously in every source point. -/
def naturalTransformationCompositionHomotopy :
    (classifyingSpaceNaturalTransformationHomotopy (α ≫ β)).toContinuousMap.HomotopyRel
      ((classifyingSpaceNaturalTransformationHomotopy α).trans
        (classifyingSpaceNaturalTransformationHomotopy β)).toContinuousMap
      {z : unitInterval × ClassifyingSpace C | z.1 = 0 ∨ z.1 = 1} where
  toFun z := functorChainBarycentric (ComposableArrows.mk₂ α β)
    (z.2.2, compositionTriangleHomotopy (z.1, z.2.1))
  continuous_toFun := by fun_prop
  map_zero_left z := by
    change functorChainBarycentric _ (z.2, compositionTriangleHomotopy (0, z.1)) = _
    rw [compositionTriangleHomotopy.apply_zero]
    exact functorChainBarycentric_two_composite α β z.2 z.1
  map_one_left z := by
    change functorChainBarycentric _ (z.2, compositionTriangleHomotopy (1, z.1)) = _
    rw [compositionTriangleHomotopy.apply_one]
    change functorChainBarycentric _
      (z.2, ((triangleEdgePath 0 1).trans (triangleEdgePath 1 2)) z.1) =
        ((classifyingSpaceNaturalTransformationHomotopy α).trans
          (classifyingSpaceNaturalTransformationHomotopy β)) z
    rw [Path.trans_apply, ContinuousMap.Homotopy.trans_apply]
    split_ifs with h
    · exact functorChainBarycentric_two_first α β z.2 _
    · exact functorChainBarycentric_two_second α β z.2 _
  prop' r z hz := by
    rcases hz with h | h
    · obtain ⟨s, x⟩ := z
      change s = 0 at h
      subst s
      change functorChainBarycentric _ (x, compositionTriangleHomotopy (r, 0)) = _
      rw [compositionTriangleHomotopy.eq_fst r (by simp)]
      exact functorChainBarycentric_two_composite α β x 0
    · obtain ⟨s, x⟩ := z
      change s = 1 at h
      subst s
      change functorChainBarycentric _ (x, compositionTriangleHomotopy (r, 1)) = _
      rw [compositionTriangleHomotopy.eq_fst r (by simp)]
      exact functorChainBarycentric_two_composite α β x 1

/-- At each source point, the comparison is a genuine relative homotopy of the original paths. -/
def naturalTransformationCompositionPathHomotopy (x : ClassifyingSpace C) :
    ((classifyingSpaceNaturalTransformationHomotopy (α ≫ β)).evalAt x).Homotopy
      (((classifyingSpaceNaturalTransformationHomotopy α).evalAt x).trans
        ((classifyingSpaceNaturalTransformationHomotopy β).evalAt x)) where
  toFun z := naturalTransformationCompositionHomotopy α β (z.1, (z.2, x))
  continuous_toFun := by fun_prop
  map_zero_left t := (naturalTransformationCompositionHomotopy α β).map_zero_left (t, x)
  map_one_left t := by
    change naturalTransformationCompositionHomotopy α β (1, (t, x)) = _
    rw [(naturalTransformationCompositionHomotopy α β).apply_one]
    change ((classifyingSpaceNaturalTransformationHomotopy α).trans
      (classifyingSpaceNaturalTransformationHomotopy β)) (t, x) =
        (((classifyingSpaceNaturalTransformationHomotopy α).evalAt x).trans
          ((classifyingSpaceNaturalTransformationHomotopy β).evalAt x)) t
    rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
    split_ifs <;> rfl
  prop' r t ht := (naturalTransformationCompositionHomotopy α β).prop' r (t, x) (by
    rcases ht with h | h
    · exact Or.inl h
    · exact Or.inr (Set.mem_singleton_iff.mp h))

end CategoryTheory.TheoremB
