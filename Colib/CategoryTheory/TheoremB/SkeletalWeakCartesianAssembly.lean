/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.TheoremB.SkeletalWeakCartesianBoundary
public import Colib.CategoryTheory.TheoremB.SkeletalWeakCartesianStageCube
public import Colib.CategoryTheory.TheoremB.SkeletalWeakCartesianStageExtraction
public import Colib.CategoryTheory.TheoremB.SkeletalWeakCartesianBoundaryAssembly
public import Colib.Topology.HomotopyPullback.WeakCoproducts

/-! # Actual successor assembly for arbitrary weak-cartesian transformations

Implementation provenance:
`Quillen/CategoryTheory/TheoremB/SkeletalWeakCartesianAssembly.lean`
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

/-- Finite boundary-face comparisons assemble over the actual cell coproduct. -/
theorem replacementAttaching_weakCartesian (htrans : TransitionWeakCartesian η)
    (n : ℕ)
    (hchart : ∀ (k : ℕ) (v : (nerve D).obj (op ⦋k⦌))
      (hv : v ∈ ((nerve D).skeleton n).obj (op ⦋k⦌)),
      ChartWeakCartesian η ((nerve D).skeleton n) v hv) :
    WeakCartesian (cellBoundaryProjection η n).hom (stageProjection η n).hom
      (attachingLeg H n).hom (attachingLeg J n).hom
      (congrArg TopCat.Hom.hom (cellAttachingSquare η n)) := by
  apply weakCartesianCofanFixedTarget
    (fun s : (nerve D).nonDegenerate n ↦ realizationFunctor.obj (replacementCellBoundary H s))
    (fun s : (nerve D).nonDegenerate n ↦ realizationFunctor.obj (replacementCellBoundary J s))
    (realizedCofan (replacementCellBoundary H)) (realizedCofan (replacementCellBoundary J))
    (realizedBisimplicialSigmaIsColimit _) (realizedBisimplicialSigmaIsColimit _)
    (stageProjection η n) (cellBoundaryProjection η n) (attachingLeg H n) (attachingLeg J n)
    (cellAttachingSquare η n)
    (fun s ↦ realizationFunctor.map (outerProductCoefficientMap
      (K := (∂Δ[n] : SSet.{u})) (η.app (s.1.obj 0))))
    (fun s ↦ realizationFunctor.map (replacementCellAttaching H s))
    (fun s ↦ realizationFunctor.map (replacementCellAttaching J s))
    (fun s ↦ realizedRestrictedSimplexChart_coefficient_square η ((nerve D).skeleton n)
      s.1 ∂Δ[n] (fun _ a ↦ replacementBaseCell_boundary s a))
  · intro s
    change realizationFunctor.map _ ≫ realizationFunctor.map _ =
      realizationFunctor.map _ ≫ realizationFunctor.map _
    rw [← realizationFunctor.map_comp, ← realizationFunctor.map_comp]
    rfl
  · intro s
    change realizationFunctor.map _ ≫ realizationFunctor.map _ = realizationFunctor.map _
    rw [← realizationFunctor.map_comp]
    rfl
  · intro s
    change realizationFunctor.map _ ≫ realizationFunctor.map _ = realizationFunctor.map _
    rw [← realizationFunctor.map_comp]
    rfl
  · exact replacementCellAttaching_weakCartesian η htrans n hchart

/-- Both outgoing conclusions follow from genuine product boundary geometry,
proved finite-face attaching comparisons, and the actual realized cube. -/
theorem successor_weakRestriction_and_chart (htrans : TransitionWeakCartesian η)
    (n : ℕ)
    (hchart : ∀ (k : ℕ) (v : (nerve D).obj (op ⦋k⦌))
      (hv : v ∈ ((nerve D).skeleton n).obj (op ⦋k⦌)),
      ChartWeakCartesian η ((nerve D).skeleton n) v hv) :
    RestrictionWeakCartesian η ((nerve D).skeleton.monotone (Nat.le_succ n)) ∧
      ∀ s : (nerve D).nonDegenerate n,
        ChartWeakCartesian η ((nerve D).skeleton (n + 1)) s.1 ((nerve D).mem_skeleton s.1) := by
  obtain ⟨hstep,hcell⟩ := successor_weakCartesian_of_incoming η n
    (replacementBoundary_weakCartesian η n)
    (replacementAttaching_weakCartesian η htrans n hchart)
  exact ⟨hstep, fun s ↦ coefficientComponentCharacteristic_weakCartesian η n hcell s⟩

end CategoryTheory.TheoremB.Skeletal
