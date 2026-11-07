/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.TheoremB.CompositionHomotopy

/-!
# Endpoint-relative cancellation of original natural-transformation tracks

The actual composable-pair simplex fills the reversed first edge followed by the
composite edge against the second edge, jointly over the entire source realization.

## Implementation provenance

Adapted from `Quillen/CategoryTheory/TheoremB/NaturalTransformationCancellation.lean`
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

/-- The actual triangle contracts the reversed-first/composite route to its second edge. -/
def cancellationTriangleHomotopy :
    ((triangleEdgePath 0 1).symm.trans (triangleEdgePath 0 2)).Homotopy
      (triangleEdgePath 1 2) :=
  Convexity.StdSimplex.pathHomotopy _ _

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {F G H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H)

/-- Cancel the original reversed first track against the composite track, continuously
in every source point and relative to both original path endpoints. -/
def naturalTransformationCancellationHomotopy :
    ((classifyingSpaceNaturalTransformationHomotopy α).symm.trans
      (classifyingSpaceNaturalTransformationHomotopy (α ≫ β))).toContinuousMap.HomotopyRel
      (classifyingSpaceNaturalTransformationHomotopy β).toContinuousMap
      {z : unitInterval × ClassifyingSpace C | z.1 = 0 ∨ z.1 = 1} where
  toFun z := functorChainBarycentric (ComposableArrows.mk₂ α β)
    (z.2.2, cancellationTriangleHomotopy (z.1, z.2.1))
  continuous_toFun := by fun_prop
  map_zero_left z := by
    change functorChainBarycentric _ (z.2, cancellationTriangleHomotopy (0, z.1)) = _
    rw [cancellationTriangleHomotopy.apply_zero]
    change functorChainBarycentric _
        (z.2, ((triangleEdgePath 0 1).symm.trans (triangleEdgePath 0 2)) z.1) =
      ((classifyingSpaceNaturalTransformationHomotopy α).symm.trans
        (classifyingSpaceNaturalTransformationHomotopy (α ≫ β))) z
    rw [Path.trans_apply, ContinuousMap.Homotopy.trans_apply]
    split_ifs with h
    · exact functorChainBarycentric_two_first α β z.2 _
    · exact functorChainBarycentric_two_composite α β z.2 _
  map_one_left z := by
    change functorChainBarycentric _ (z.2, cancellationTriangleHomotopy (1, z.1)) = _
    rw [cancellationTriangleHomotopy.apply_one]
    exact functorChainBarycentric_two_second α β z.2 z.1
  prop' r z hz := by
    rcases hz with h | h
    · obtain ⟨s, x⟩ := z
      change s = 0 at h
      subst s
      change functorChainBarycentric _ (x, cancellationTriangleHomotopy (r, 0)) = _
      rw [cancellationTriangleHomotopy.source]
      change functorChainBarycentric _ (x, Convexity.StdSimplex.single 1) =
        ((classifyingSpaceNaturalTransformationHomotopy α).symm.trans
          (classifyingSpaceNaturalTransformationHomotopy (α ≫ β))) (0, x)
      rw [ContinuousMap.Homotopy.apply_zero]
      simpa only [triangleEdge_zero, ContinuousMap.Homotopy.apply_zero,
        ContinuousMap.Homotopy.symm_apply, ContinuousMap.Homotopy.apply_one] using
        functorChainBarycentric_two_second α β x 0
    · obtain ⟨s, x⟩ := z
      change s = 1 at h
      subst s
      change functorChainBarycentric _ (x, cancellationTriangleHomotopy (r, 1)) = _
      rw [cancellationTriangleHomotopy.target]
      change functorChainBarycentric _ (x, Convexity.StdSimplex.single 2) =
        ((classifyingSpaceNaturalTransformationHomotopy α).symm.trans
          (classifyingSpaceNaturalTransformationHomotopy (α ≫ β))) (1, x)
      rw [ContinuousMap.Homotopy.apply_one]
      simpa only [triangleEdge_one, ContinuousMap.Homotopy.apply_one] using
        functorChainBarycentric_two_second α β x 1

/-- Evaluation retains the exact reversed and concatenated original tracks. -/
def naturalTransformationCancellationPathHomotopy (x : ClassifyingSpace C) :
    (((classifyingSpaceNaturalTransformationHomotopy α).evalAt x).symm.trans
      ((classifyingSpaceNaturalTransformationHomotopy (α ≫ β)).evalAt x)).Homotopy
      ((classifyingSpaceNaturalTransformationHomotopy β).evalAt x) where
  toFun z := naturalTransformationCancellationHomotopy α β (z.1, (z.2, x))
  continuous_toFun := by fun_prop
  map_zero_left t := by
    change naturalTransformationCancellationHomotopy α β (0, (t, x)) = _
    rw [(naturalTransformationCancellationHomotopy α β).apply_zero]
    change ((classifyingSpaceNaturalTransformationHomotopy α).symm.trans
      (classifyingSpaceNaturalTransformationHomotopy (α ≫ β))) (t, x) =
      (((classifyingSpaceNaturalTransformationHomotopy α).evalAt x).symm.trans
        ((classifyingSpaceNaturalTransformationHomotopy (α ≫ β)).evalAt x)) t
    rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
    split_ifs <;> rfl
  map_one_left t := (naturalTransformationCancellationHomotopy α β).map_one_left (t, x)
  prop' r t ht := by
    change naturalTransformationCancellationHomotopy α β (r, (t, x)) = _
    rw [(naturalTransformationCancellationHomotopy α β).eq_fst r (by
      rcases ht with h | h
      · exact Or.inl h
      · exact Or.inr (Set.mem_singleton_iff.mp h))]
    change ((classifyingSpaceNaturalTransformationHomotopy α).symm.trans
      (classifyingSpaceNaturalTransformationHomotopy (α ≫ β))) (t, x) =
      (((classifyingSpaceNaturalTransformationHomotopy α).evalAt x).symm.trans
        ((classifyingSpaceNaturalTransformationHomotopy (α ≫ β)).evalAt x)) t
    rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
    split_ifs <;> rfl

end CategoryTheory.TheoremB
