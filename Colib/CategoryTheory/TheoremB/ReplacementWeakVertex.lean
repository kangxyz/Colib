/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.TheoremB.StageOneCartesian

public import Colib.CategoryTheory.TheoremB.SkeletalWeakCartesianInduction
public import Colib.CategoryTheory.TheoremA.ReplacementStageOne
public import Colib.Topology.HomotopyPullback.CoproductAssembly

/-!
# Weak comparison at an actual replacement vertex

The first skeletal stage is the genuine coproduct of diagram values. Its
component square is homotopy cartesian for arbitrary coefficient maps. Pasting
with the weak stage-to-total theorem gives the original vertex comparison,
retaining the realized inclusion, coefficient map, and entire constant path.


Implementation provenance:
`Quillen/CategoryTheory/TheoremB/ReplacementWeakVertex.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.TheoremA


noncomputable section
open Topology TopCat SSet Topology.HomotopyPullback
open CategoryTheory Limits Opposite
open scoped Simplicial Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.TheoremB.Skeletal
open TheoremA
variable {D : Type u} [SmallCategory D] {H J : D ⥤ SSet.{u}} (η : H ⟶ J)

/-- The original replacement vertex square commutes strictly. -/
theorem replacementVertex_square (d : D) :
    (SSet.toTop.map (diagonalMap (simplicialReplacementMap η))).hom.comp
      (SSet.toTop.map (replacementVertexInclusion H d)).hom =
    (SSet.toTop.map (replacementVertexInclusion J d)).hom.comp
      (SSet.toTop.map (η.app d)).hom := by
  change (SSet.toTop.map (replacementVertexInclusion H d) ≫
      SSet.toTop.map (diagonalMap (simplicialReplacementMap η))).hom =
    (SSet.toTop.map (η.app d) ≫ SSet.toTop.map (replacementVertexInclusion J d)).hom
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

/-- Weak transition comparisons imply complete weakness of the actual vertex comparison. -/
theorem replacementVertexComparison_isWeakHomotopyEquivalence
    (htrans : TransitionWeakCartesian η) (d : D) :
    IsWeakHomotopyEquivalence (HomotopyPullback.comparison
      (SSet.toTop.map (diagonalMap (simplicialReplacementMap η))).hom
      (SSet.toTop.map (replacementVertexInclusion J d)).hom
      (SSet.toTop.map (η.app d)).hom
      (SSet.toTop.map (replacementVertexInclusion H d)).hom
      (replacementVertex_square η d)) := by
  have h := (realizedReplacementStageOneVertex_cartesian η d).weak.paste
    (replacementSkeletonComparison_isWeakHomotopyEquivalence η htrans 1)
  apply h.congr rfl
    (congrArg TopCat.Hom.hom (realizedReplacementSkeleton_colimitMap η))
  · apply ContinuousMap.ext
    intro x
    change (SSet.toTop.map (SSet.simplicialSigmaι (fun d : D ↦ H.obj d) d ≫
      vertexCoproductToStageOne H) ≫
      SSet.toTop.map (diagonalMap (replacementRestrictionι H ((nerve D).skeleton 1)))) x = _
    rw [← Functor.map_comp, Category.assoc, vertexCoproductToStageOne_ι]
    rfl
  · apply ContinuousMap.ext
    intro x
    change (SSet.toTop.map (SSet.simplicialSigmaι (fun d : D ↦ J.obj d) d ≫
      vertexCoproductToStageOne J) ≫
      SSet.toTop.map (diagonalMap (replacementRestrictionι J ((nerve D).skeleton 1)))) x = _
    rw [← Functor.map_comp, Category.assoc, vertexCoproductToStageOne_ι]
    rfl

end CategoryTheory.TheoremB.Skeletal
