/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyPullback.WeakCalculus
public import Colib.CategoryTheory.TheoremB.SkeletalCartesianStageCube
public import Colib.Topology.Realization.DoubleCylinderCompactGraph
public import Colib.Topology.HomotopyPullback.WeakPushout

/-!
# The weak-input cube of the actual replacement skeleta

The incoming and outgoing comparisons are the original constant-path maps.
The target graph hypothesis is discharged on the literal realized diagonal
simplicial span; no realization-product identification or graph assumption is
added. This applies to a general natural transformation, not only to a point
augmentation. Both incoming faces still have to be proved by chart induction.


Implementation provenance:
`Quillen/CategoryTheory/TheoremB/SkeletalWeakCartesianStageCube.lean`
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

/-- The exact target cell/attaching span is already a realized simplicial
span after taking diagonals, so all compact test graphs are genuinely closed. -/
theorem successorCylinder_compactMap_isClosed_graph (n : ℕ)
    {K : Type u} [TopologicalSpace K] [CompactSpace K]
    (b : C(K, DoubleCylinder.Cylinder (boundaryLeg J n) (attachingLeg J n))) :
    IsClosed (Set.ofPred (fun z : K × DoubleCylinder.Cylinder
      (boundaryLeg J n) (attachingLeg J n) ↦ b z.1 = z.2)) :=
  DoubleCylinder.compactMap_isClosed_graph
    (diagonalMap (replacementCellsBoundaryι J n))
    (diagonalMap (replacementCellsAttaching J n))
    (DoubleCylinder.cylinderSquare (boundaryLeg J n) (attachingLeg J n)) b

/-- The actual replacement pushout propagates both weak-cartesian
comparisons from its two original incoming comparisons. -/
theorem successor_weakCartesian_of_incoming (n : ℕ)
    (hboundary : WeakCartesian (cellBoundaryProjection η n).hom (cellProjection η n).hom
      (boundaryLeg H n).hom (boundaryLeg J n).hom (congrArg TopCat.Hom.hom (cellBoundarySquare η
        n)))
    (hattaching : WeakCartesian (cellBoundaryProjection η n).hom (stageProjection η n).hom
      (attachingLeg H n).hom (attachingLeg J n).hom (congrArg TopCat.Hom.hom (cellAttachingSquare η
        n))) :
    WeakCartesian (stageProjection η n).hom (stageProjection η (n+1)).hom
      (stageStep H n).hom (stageStep J n).hom (congrArg TopCat.Hom.hom (stageStepSquare η n)) ∧
    WeakCartesian (cellProjection η n).hom (stageProjection η (n+1)).hom
      (characteristicLeg H n).hom (characteristicLeg J n).hom
      (congrArg TopCat.Hom.hom (cellCharacteristicSquare η n)) := by
  let sq := (realizedReplacementSkeleton_isPushout H n).flip
  let sq' := (realizedReplacementSkeleton_isPushout J n).flip
  have hi := homotopyExtensionProperty_replacementCellsBoundary H n
  have hi' := homotopyExtensionProperty_replacementCellsBoundary J n
  have hgraph := fun (K : Type u) [TopologicalSpace K] [CompactSpace K] [LocallyCompactSpace K]
      (b : C(K,DoubleCylinder.Cylinder (boundaryLeg J n) (attachingLeg J n))) ↦
    successorCylinder_compactMap_isClosed_graph (J := J) n b
  constructor
  · exact CartesianPushout.rightComparison_isWeakHomotopyEquivalence sq sq'
      (cellBoundaryProjection η n) (cellProjection η n) (stageProjection η n)
      (stageProjection η (n+1)) (cellBoundarySquare η n) (cellAttachingSquare η n)
      (cellCharacteristicSquare η n) (stageStepSquare η n) hi hi' hgraph hboundary hattaching
  · exact CartesianPushout.leftComparison_isWeakHomotopyEquivalence sq sq'
      (cellBoundaryProjection η n) (cellProjection η n) (stageProjection η n)
      (stageProjection η (n+1)) (cellBoundarySquare η n) (cellAttachingSquare η n)
      (cellCharacteristicSquare η n) (stageStepSquare η n) hi hi' hgraph hboundary hattaching

end CategoryTheory.TheoremB.Skeletal
