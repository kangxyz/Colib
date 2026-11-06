/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremB.SkeletalCartesianStageRestriction
public import Colib.Topology.HomotopyPullback.CoordinateTransport

/-! Extract the old-stage and individual characteristic-chart comparisons
from the two outgoing faces of the actual replacement attachment cube. -/
/-! Implementation provenance: adapted from
`Quillen/CategoryTheory/TheoremB/SkeletalCartesianStageExtraction.lean`
at c561118b7795eb9780be9ed391c3251d6a4d0afd, retaining the actual replacement charts,
base restrictions and canonical comparisons. -/
@[expose] public section

open CategoryTheory.TheoremA SSet Topology.HomotopyPullback
open CategoryTheory.TheoremB


noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial Topology unitInterval
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.TheoremB.Skeletal
open TheoremA
variable {D : Type u} [SmallCategory D] (H : D ⥤ SSet.{u})

/-- The vertical cell projection preserves each actual coproduct summand. -/
theorem componentCell_square {n : ℕ} (s : (nerve D).nonDegenerate n) :
    realizationFunctor.map (bisimplicialSigmaι (replacementCell H) s) ≫
      cellProjection (replacementPointAugmentation H) n =
    realizationFunctor.map (outerProductCoefficientMap
      (K := (Δ[n] : SSet.{u})) ((replacementPointAugmentation H).app (s.1.obj 0))) ≫
      realizationFunctor.map (bisimplicialSigmaι (replacementCell pointDiagram) s) := by
  change realizationFunctor.map _ ≫ realizationFunctor.map _ =
    realizationFunctor.map _ ≫ realizationFunctor.map _
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  rfl

/-- Component inclusions are cartesian over the corresponding actual
point-valued component, regardless of the coefficient space. -/
theorem componentCell_cartesian (n : ℕ) (s : (nerve D).nonDegenerate n) :
    Cartesian (realizationFunctor.map (outerProductCoefficientMap
      (K := (Δ[n] : SSet.{u})) ((replacementPointAugmentation H).app (s.1.obj 0)))).hom
      (cellProjection (replacementPointAugmentation H) n).hom
      (realizationFunctor.map (bisimplicialSigmaι (replacementCell H) s)).hom
      (realizationFunctor.map (bisimplicialSigmaι (replacementCell pointDiagram) s)).hom
      (congrArg TopCat.Hom.hom (componentCell_square H s)) :=
  cartesianCofanComponent
    (fun s : (nerve D).nonDegenerate n ↦ realizationFunctor.obj (replacementCell H s))
    (fun s : (nerve D).nonDegenerate n ↦ realizationFunctor.obj (replacementCell pointDiagram s))
    (realizedCofan (replacementCell H)) (realizedCofan (replacementCell pointDiagram))
    (realizedBisimplicialSigmaIsColimit _) (realizedBisimplicialSigmaIsColimit _)
    (cellProjection (replacementPointAugmentation H) n)
    (fun s ↦ realizationFunctor.map (outerProductCoefficientMap
      (K := (Δ[n] : SSet.{u})) ((replacementPointAugmentation H).app (s.1.obj 0))))
    (fun s ↦ componentCell_square H s) s

/-- The individual actual characteristic square commutes before any
change of point-valued coordinates. -/
theorem componentCharacteristic_square {n : ℕ} (s : (nerve D).nonDegenerate n) :
    realizationFunctor.map (replacementCellCharacteristic H s) ≫
      stageProjection (replacementPointAugmentation H) (n + 1) =
    realizationFunctor.map (outerProductCoefficientMap
      (K := (Δ[n] : SSet.{u})) ((replacementPointAugmentation H).app (s.1.obj 0))) ≫
      realizationFunctor.map (replacementCellCharacteristic pointDiagram s) := by
  change realizationFunctor.map _ ≫ realizationFunctor.map _ =
    realizationFunctor.map _ ≫ realizationFunctor.map _
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg realizationFunctor.map
    (simplexChart_coefficient H (replacementPointAugmentation H)
      ((nerve D).skeleton (n + 1)) s.1 ((nerve D).mem_skeleton s.1))

/-- The outgoing whole-cell face supplies each actual characteristic
chart by cartesian coproduct-component inclusion and pasting. -/
theorem componentCharacteristic_cartesian (n : ℕ)
    (h : Cartesian (cellProjection (replacementPointAugmentation H) n).hom
      (stageProjection (replacementPointAugmentation H) (n + 1)).hom
      (characteristicLeg H n).hom (characteristicLeg pointDiagram n).hom
      (congrArg TopCat.Hom.hom (cellCharacteristicSquare (replacementPointAugmentation H) n)))
    (s : (nerve D).nonDegenerate n) :
    Cartesian (realizationFunctor.map (outerProductCoefficientMap
      (K := (Δ[n] : SSet.{u})) ((replacementPointAugmentation H).app (s.1.obj 0)))).hom
      (stageProjection (replacementPointAugmentation H) (n + 1)).hom
      (realizationFunctor.map (replacementCellCharacteristic H s)).hom
      (realizationFunctor.map (replacementCellCharacteristic pointDiagram s)).hom
      (congrArg TopCat.Hom.hom (componentCharacteristic_square H s)) := by
  have hpaste := (componentCell_cartesian H n s).paste h
  have hf : realizationFunctor.map (bisimplicialSigmaι (replacementCell H) s) ≫
      characteristicLeg H n = realizationFunctor.map (replacementCellCharacteristic H s) := by
    change realizationFunctor.map _ ≫ realizationFunctor.map _ = realizationFunctor.map _
    rw [← CategoryTheory.Functor.map_comp]
    rfl
  have hg : realizationFunctor.map (bisimplicialSigmaι (replacementCell pointDiagram) s) ≫
      characteristicLeg pointDiagram n =
        realizationFunctor.map (replacementCellCharacteristic pointDiagram s) := by
    change realizationFunctor.map _ ≫ realizationFunctor.map _ = realizationFunctor.map _
    rw [← CategoryTheory.Functor.map_comp]
    rfl
  exact hpaste.congr rfl rfl (congrArg TopCat.Hom.hom hf) (congrArg TopCat.Hom.hom hg)

/-- Changing only the point-valued coordinates of the actual individual
characteristic square yields the canonical simplex-chart comparison. -/
theorem chartCartesian_of_componentCharacteristic (n : ℕ)
    (s : (nerve D).nonDegenerate n)
    (h : Cartesian (realizationFunctor.map (outerProductCoefficientMap
      (K := (Δ[n] : SSet.{u})) ((replacementPointAugmentation H).app (s.1.obj 0)))).hom
      (stageProjection (replacementPointAugmentation H) (n + 1)).hom
      (realizationFunctor.map (replacementCellCharacteristic H s)).hom
      (realizationFunctor.map (replacementCellCharacteristic pointDiagram s)).hom
      (congrArg TopCat.Hom.hom (componentCharacteristic_square H s))) :
    ChartCartesian H ((nerve D).skeleton (n + 1)) s.1 ((nerve D).mem_skeleton s.1) := by
  apply cartesianToCoordinates
    (realizationFunctor.map (outerProductCoefficientMap
      (K := (Δ[n] : SSet.{u})) ((replacementPointAugmentation H).app (s.1.obj 0)))).hom
    (stageProjection (replacementPointAugmentation H) (n + 1)).hom
    (realizationFunctor.map (replacementCellCharacteristic H s)).hom
    (realizationFunctor.map (replacementCellCharacteristic pointDiagram s)).hom
    (congrArg TopCat.Hom.hom (componentCharacteristic_square H s))
    (SSet.toTop.map (outerProjection Δ[n] (H.obj (s.1.obj 0)))).hom
    (SSet.toTop.map (restrictionProjection H ((nerve D).skeleton (n + 1)))).hom
    (realizationFunctor.map (replacementCellCharacteristic H s)).hom
    (SSet.toTop.map (baseSimplexMap ((nerve D).skeleton (n + 1)) s.1
      ((nerve D).mem_skeleton s.1))).hom
    (congrArg TopCat.Hom.hom (realizedSimplexChart_square H
      ((nerve D).skeleton (n + 1)) s.1 ((nerve D).mem_skeleton s.1)))
    (Homeomorph.refl _) (Homeomorph.refl _)
    (pointOuterHomeomorph (Δ[n] : SSet.{u}))
    (pointRestrictionHomeomorph ((nerve D).skeleton (n + 1)))
  · change (SSet.toTop.map (outerProjection _ _)).hom =
      (SSet.toTop.map (diagonalMap (outerProductCoefficientMap _)) ≫
        SSet.toTop.map (pointOuterIso _).hom).hom
    rw [← CategoryTheory.Functor.map_comp]
    rfl
  · exact congrArg TopCat.Hom.hom (pointRestrictionIso_projectionTower H (n + 1)).symm
  · rfl
  · change (SSet.toTop.map (pointOuterIso _).hom ≫ SSet.toTop.map (baseSimplexMap _ _ _)).hom =
      (SSet.toTop.map (diagonalMap (replacementCellCharacteristic pointDiagram s)) ≫
        SSet.toTop.map (pointRestrictionIso _).hom).hom
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    rfl
  · exact h

/-- The two genuinely derived successor conclusions needed by simultaneous
skeletal induction, in actual base-restriction and simplex-chart coordinates. -/
theorem successor_restriction_and_chart
    (htrans : ∀ ⦃d e : D⦄ (f : d ⟶ e),
      ∃ E : ContinuousMap.HomotopyEquiv |H.obj d| |H.obj e|,
        E.toFun = (SSet.toTop.map (H.map f)).hom)
    (n : ℕ)
    (hchart : ∀ (k : ℕ) (v : (nerve D).obj (op ⦋k⦌))
      (hv : v ∈ ((nerve D).skeleton n).obj (op ⦋k⦌)),
      ChartCartesian H ((nerve D).skeleton n) v hv) :
    RestrictionCartesian H ((nerve D).skeleton.monotone (Nat.le_succ n)) ∧
      ∀ s : (nerve D).nonDegenerate n,
        ChartCartesian H ((nerve D).skeleton (n + 1)) s.1 ((nerve D).mem_skeleton s.1) := by
  obtain ⟨hstep, hcell⟩ := replacementSuccessor_cartesian H htrans n hchart
  exact ⟨restrictionCartesian_of_stageCartesian H n hstep,
    fun s ↦ chartCartesian_of_componentCharacteristic H n s
      (componentCharacteristic_cartesian H n hcell s)⟩

end CategoryTheory.TheoremB.Skeletal
