/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyPullback.Cartesian
public import Colib.Topology.HomotopyPullback.Pushout
public import Colib.CategoryTheory.TheoremA.SkeletalCofibrations
public import Colib.CategoryTheory.TheoremA.SkeletalNaturality

/-! Simultaneous homotopy-cartesian induction in the actual replacement
skeleton tower. The finite cube is applied only after both incoming
boundary comparisons have been proved. -/
/-! Implementation source: `Quillen/CategoryTheory/TheoremB/SkeletalCartesianStageCube.lean`
at c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual realized replacement
attachments and prescribed canonical comparisons are retained. -/
@[expose] public section

open CategoryTheory.TheoremA SSet Topology.HomotopyPullback


noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial Topology unitInterval
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.TheoremB.Skeletal
open TheoremA
variable {D : Type u} [SmallCategory D] {H J : D ⥤ SSet.{u}} (η : H ⟶ J)

/-- The functor that takes the diagonal of a bisimplicial set and then its topological realization.
-/
abbrev realizationFunctor : (SimplexCategoryᵒᵖ ⥤ SSet.{u}) ⥤ TopCat.{u} :=
  diagonalFunctor ⋙ SSet.toTop
/-- The realized map between the dimension-`n` replacement cells induced by the coefficient
transformation `η : H ⟶ J`. -/
abbrev cellProjection (n : ℕ) := realizationFunctor.map (replacementCellsMap η n)
/-- The realized map between the boundaries of the dimension-`n` replacement cells induced by `η :
H ⟶ J`. -/
abbrev cellBoundaryProjection (n : ℕ) := realizationFunctor.map (replacementCellBoundariesMap η n)
/-- The map from the realized `n`th replacement skeleton for `H` to that for `J`, induced by `η`. -/
abbrev stageProjection (n : ℕ) := (realizedReplacementSkeletonMap η).app n
/-- The realized boundary inclusion of the dimension-`n` replacement cells for `H`. -/
abbrev boundaryLeg (H : D ⥤ SSet.{u}) (n : ℕ) :=
  realizationFunctor.map (replacementCellsBoundaryι H n)
/-- The realized attaching map from the dimension-`n` cell boundaries to the `n`th replacement
skeleton for `H`. -/
abbrev attachingLeg (H : D ⥤ SSet.{u}) (n : ℕ) :=
  realizationFunctor.map (replacementCellsAttaching H n)
/-- The realized characteristic map from the dimension-`n` cells to the next replacement skeleton
for `H`. -/
abbrev characteristicLeg (H : D ⥤ SSet.{u}) (n : ℕ) :=
  realizationFunctor.map (replacementCellsCharacteristic H n)
/-- The inclusion from the realized `n`th replacement skeleton to the realized `(n + 1)`st skeleton
for `H`. -/
abbrev stageStep (H : D ⥤ SSet.{u}) (n : ℕ) :=
  (realizedReplacementSkeleton H).map (homOfLE (Nat.le_succ n))

theorem cellBoundarySquare (n : ℕ) :
    boundaryLeg H n ≫ cellProjection η n = cellBoundaryProjection η n ≫ boundaryLeg J n := by
  change realizationFunctor.map _ ≫ realizationFunctor.map _ =
    realizationFunctor.map _ ≫ realizationFunctor.map _
  rw [← realizationFunctor.map_comp, ← realizationFunctor.map_comp, replacementCellsMap_boundary]

theorem cellAttachingSquare (n : ℕ) :
    attachingLeg H n ≫ stageProjection η n = cellBoundaryProjection η n ≫ attachingLeg J n := by
  change realizationFunctor.map _ ≫ realizationFunctor.map _ =
    realizationFunctor.map _ ≫ realizationFunctor.map _
  rw [← realizationFunctor.map_comp, ← realizationFunctor.map_comp, replacementCellsMap_attaching]

theorem cellCharacteristicSquare (n : ℕ) :
    characteristicLeg H n ≫ stageProjection η (n+1) = cellProjection η n ≫ characteristicLeg J n :=
      by
  change realizationFunctor.map _ ≫ realizationFunctor.map _ =
    realizationFunctor.map _ ≫ realizationFunctor.map _
  rw [← realizationFunctor.map_comp, ← realizationFunctor.map_comp,
    replacementCellsMap_characteristic]

theorem stageStepSquare (n : ℕ) :
    stageStep H n ≫ stageProjection η (n+1) = stageProjection η n ≫ stageStep J n :=
  (realizedReplacementSkeletonMap η).naturality (homOfLE (Nat.le_succ n))

/-- The genuine finite cube gives both outgoing stage/cell comparisons,
without hiding either of the two incoming comparison obligations. -/
theorem successor_cartesian_of_incoming (n : ℕ)
    (hboundary : Cartesian (cellBoundaryProjection η n).hom (cellProjection η n).hom
      (boundaryLeg H n).hom (boundaryLeg J n).hom (congrArg TopCat.Hom.hom (cellBoundarySquare η
        n)))
    (hattaching : Cartesian (cellBoundaryProjection η n).hom (stageProjection η n).hom
      (attachingLeg H n).hom (attachingLeg J n).hom (congrArg TopCat.Hom.hom (cellAttachingSquare η
        n))) :
    Cartesian (stageProjection η n).hom (stageProjection η (n+1)).hom
      (stageStep H n).hom (stageStep J n).hom (congrArg TopCat.Hom.hom (stageStepSquare η n)) ∧
    Cartesian (cellProjection η n).hom (stageProjection η (n+1)).hom
      (characteristicLeg H n).hom (characteristicLeg J n).hom
      (congrArg TopCat.Hom.hom (cellCharacteristicSquare η n)) := by
  let sq := (realizedReplacementSkeleton_isPushout H n).flip
  let sq' := (realizedReplacementSkeleton_isPushout J n).flip
  have hi := homotopyExtensionProperty_replacementCellsBoundary H n
  have hi' := homotopyExtensionProperty_replacementCellsBoundary J n
  refine ⟨?_,?_⟩
  · exact ⟨TopCat.CartesianPushout.rightHomotopyEquiv sq sq'
      (cellBoundaryProjection η n) (cellProjection η n) (stageProjection η n)
      (stageProjection η (n+1)) (cellBoundarySquare η n) (cellAttachingSquare η n)
      (cellCharacteristicSquare η n) (stageStepSquare η n) hi hi'
      hboundary.equiv hboundary.equiv_toFun hattaching.equiv hattaching.equiv_toFun,
      TopCat.CartesianPushout.rightHomotopyEquiv_toFun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _⟩
  · exact ⟨TopCat.CartesianPushout.leftHomotopyEquiv sq sq'
      (cellBoundaryProjection η n) (cellProjection η n) (stageProjection η n)
      (stageProjection η (n+1)) (cellBoundarySquare η n) (cellAttachingSquare η n)
      (cellCharacteristicSquare η n) (stageStepSquare η n) hi hi'
      hboundary.equiv hboundary.equiv_toFun hattaching.equiv hattaching.equiv_toFun,
      TopCat.CartesianPushout.leftHomotopyEquiv_toFun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _⟩

end CategoryTheory.TheoremB.Skeletal
