/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.ClassifyingSpace.FunctorChain

/-!
# Endpoint-relative inverse natural-isomorphism coherence

Implementation source: `Quillen/CategoryTheory/TheoremB/StructuredIsoHomotopy.lean` and
`Quillen/Topology/ClassifyingSpace/FunctorChain.lean`
at c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual simplex families,
path coordinates, and endpoint data are retained under native ownership.
-/
@[expose] public section
noncomputable section
open Topology CategoryTheory SSet Opposite MonoidalCategory CartesianMonoidalCategory Convexity
open scoped Simplicial Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
/-- The homotopy from an inverse natural isomorphism agrees with the reversed
forward homotopy through an actual two-parameter homotopy, relative to both
ends of the path parameter. It is jointly continuous in every source point. -/
def naturalIsoInverseHomotopy {F G : C ⥤ D} (e : F ≅ G) :
    (classifyingSpaceNaturalTransformationHomotopy e.inv).toContinuousMap.HomotopyRel
      (classifyingSpaceNaturalTransformationHomotopy e.hom).symm.toContinuousMap
      (fun z : unitInterval × ClassifyingSpace C ↦ z.1 = 0 ∨ z.1 = 1) where
  toFun z := functorChainBarycentric (ComposableArrows.mk₂ e.hom e.inv)
    (z.2.2, inverseTriangleParameter z.1 z.2.1)
  continuous_toFun := by fun_prop
  map_zero_left z := by
    change functorChainBarycentric _ (z.2, inverseTriangleParameter 0 z.1) = _
    rw [inverseTriangleParameter_zero, functorChainBarycentric_two_second]
    rfl
  map_one_left z := by
    change functorChainBarycentric _ (z.2, inverseTriangleParameter 1 z.1) = _
    rw [inverseTriangleParameter_one, functorChainBarycentric_two_first]
    rfl
  prop' s z hz := by
    rcases z with ⟨t, x⟩
    rcases hz with ht | ht
    · change t = 0 at ht
      subst t
      change functorChainBarycentric _ (x, inverseTriangleParameter s 0) = _
      rw [inverseTriangleParameter_source, ← triangleEdge_zero 1 2,
        functorChainBarycentric_two_second]
      rfl
    · change t = 1 at ht
      subst t
      change functorChainBarycentric _ (x, inverseTriangleParameter s 1) = _
      rw [inverseTriangleParameter_target, functorChainBarycentric_two_composite,
        e.hom_inv_id, classifyingHomotopy_id]
      exact (classifyingSpaceNaturalTransformationHomotopy e.inv).map_one_left x |>.symm

/-- Pathwise form of the inverse-isomorphism coherence, with endpoints fixed. -/
def naturalIsoInversePathHomotopy {F G : C ⥤ D} (e : F ≅ G) (x : ClassifyingSpace C) :
    ((classifyingSpaceNaturalTransformationHomotopy e.inv).evalAt x).Homotopy
      ((classifyingSpaceNaturalTransformationHomotopy e.hom).evalAt x).symm where
  toFun z := naturalIsoInverseHomotopy e (z.1, (z.2, x))
  continuous_toFun := by fun_prop
  map_zero_left t := (naturalIsoInverseHomotopy e).map_zero_left (t, x)
  map_one_left t := (naturalIsoInverseHomotopy e).map_one_left (t, x)
  prop' s t ht := (naturalIsoInverseHomotopy e).prop' s (t, x) (by
    rcases ht with ht | ht
    · exact Or.inl ht
    · exact Or.inr (Set.mem_singleton_iff.mp ht))
/-- The inverse-isomorphism coherence really fixes a vertex under the thin
zero-target condition; this is stronger than merely fixing the path endpoints. -/
theorem naturalIsoInverseHomotopy_vertex_of_subsingleton {F G : C ⥤ D}
    (e : F ≅ G) (c : C) (d : D) (hF : F.obj c = d) (hG : G.obj c = d)
    (hthin : ∀ Y : D, Subsingleton (Y ⟶ d)) (s t : unitInterval) :
    naturalIsoInverseHomotopy e (s, (t, classifyingSpacePoint c)) = classifyingSpacePoint d := by
  change functorChainRealization (ComposableArrows.mk₂ e.hom e.inv)
    (classifyingSpacePoint c,
      (FiniteSimplexAdapter.toTopHomeomorph ⦋2⦌).symm (inverseTriangleParameter s t)) = _
  apply functorChainRealization_vertex_of_subsingleton _ c d _ hthin
  intro i
  fin_cases i
  · exact hF
  · exact hG
  · exact hF

end CategoryTheory
