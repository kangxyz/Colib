/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremB.SkeletalCartesianBoundary
public import Colib.CategoryTheory.TheoremB.SkeletalCartesianStageCube
public import Colib.CategoryTheory.TheoremB.SkeletalBoundary

/-! # Actual replacement-stage cartesian cube assembly -/
/-! Implementation provenance: adapted from
`Quillen/CategoryTheory/TheoremB/SkeletalCartesianAssembly.lean`
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
open TheoremA TheoremB Topology.Realization.CartesianDomains

variable {D : Type u} [SmallCategory D] (H : D ⥤ SSet.{u})

/-- The exact component square before assembling the attaching coproduct. -/
theorem componentAttaching_square {n : ℕ} (s : (nerve D).nonDegenerate n) :
    realizationFunctor.map (replacementCellAttaching H s) ≫
      stageProjection (replacementPointAugmentation H) n =
    realizationFunctor.map (outerProductCoefficientMap
      (K := (∂Δ[n] : SSet.{u})) ((replacementPointAugmentation H).app (s.1.obj 0))) ≫
      realizationFunctor.map (replacementCellAttaching pointDiagram s) := by
  change realizationFunctor.map _ ≫ realizationFunctor.map _ =
    realizationFunctor.map _ ≫ realizationFunctor.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg realizationFunctor.map
  ext p q x : 5
  apply congrArg (Sigma.mk _)
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app ((replacementPointAugmentation H).naturality
      (firstVertexEdge x.1.1.down.op s.1)) q) x.2

/-- Finite boundary-chart descent supplies each incoming component square
in the original point-replacement coordinates. -/
theorem componentAttaching_cartesian
    (htrans : ∀ ⦃d e : D⦄ (f : d ⟶ e),
      ∃ E : ContinuousMap.HomotopyEquiv |H.obj d| |H.obj e|,
        E.toFun = (SSet.toTop.map (H.map f)).hom)
    (n : ℕ)
    (hchart : ∀ (k : ℕ) (v : (nerve D).obj (op ⦋k⦌))
      (hv : v ∈ ((nerve D).skeleton n).obj (op ⦋k⦌)),
      ChartCartesian H ((nerve D).skeleton n) v hv)
    (s : (nerve D).nonDegenerate n) :
    Cartesian (realizationFunctor.map (outerProductCoefficientMap
      (K := (∂Δ[n] : SSet.{u})) ((replacementPointAugmentation H).app (s.1.obj 0)))).hom
      (stageProjection (replacementPointAugmentation H) n).hom
      (realizationFunctor.map (replacementCellAttaching H s)).hom
      (realizationFunctor.map (replacementCellAttaching pointDiagram s)).hom
      (congrArg TopCat.Hom.hom (componentAttaching_square H s)) := by
  apply cartesianOfCoordinates _ _ _ _ _
    (domainProjection (H.obj (s.1.obj 0)) (∂Δ[n] : SSet.{u})).hom
    (SSet.toTop.map (restrictionProjection H ((nerve D).skeleton n))).hom
    (realizationFunctor.map (replacementCellAttaching H s)).hom
    (SSet.toTop.map (boundaryBaseMap s)).hom _
    (Homeomorph.refl _) (Homeomorph.refl _)
    (pointOuterHomeomorph (∂Δ[n] : SSet.{u}))
    (pointRestrictionHomeomorph ((nerve D).skeleton n))
  · change (SSet.toTop.map (outerProjection _ _)).hom =
      (SSet.toTop.map (diagonalMap (outerProductCoefficientMap _)) ≫
        SSet.toTop.map (pointOuterIso _).hom).hom
    rw [← Functor.map_comp]
    rfl
  · exact congrArg TopCat.Hom.hom (pointRestrictionIso_projectionTower H n).symm
  · rfl
  · change (SSet.toTop.map (pointOuterIso _).hom ≫ SSet.toTop.map (boundaryBaseMap s)).hom =
      (SSet.toTop.map (diagonalMap (replacementCellAttaching pointDiagram s)) ≫
        SSet.toTop.map (pointRestrictionIso _).hom).hom
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  · exact replacementCellAttaching_cartesian H htrans n hchart s

/-- The entire incoming attaching face follows from the proved finite
boundary comparisons and the universal property of the actual coproduct. -/
theorem replacementAttaching_cartesian
    (htrans : ∀ ⦃d e : D⦄ (f : d ⟶ e),
      ∃ E : ContinuousMap.HomotopyEquiv |H.obj d| |H.obj e|,
        E.toFun = (SSet.toTop.map (H.map f)).hom)
    (n : ℕ)
    (hchart : ∀ (k : ℕ) (v : (nerve D).obj (op ⦋k⦌))
      (hv : v ∈ ((nerve D).skeleton n).obj (op ⦋k⦌)),
      ChartCartesian H ((nerve D).skeleton n) v hv) :
    Cartesian (cellBoundaryProjection (replacementPointAugmentation H) n).hom
      (stageProjection (replacementPointAugmentation H) n).hom
      (attachingLeg H n).hom (attachingLeg pointDiagram n).hom
      (congrArg TopCat.Hom.hom (cellAttachingSquare (replacementPointAugmentation H) n)) := by
  apply cartesianCofanFixedTarget
    (fun s : (nerve D).nonDegenerate n ↦ realizationFunctor.obj (replacementCellBoundary H s))
    (fun s : (nerve D).nonDegenerate n ↦ realizationFunctor.obj (replacementCellBoundary
      pointDiagram s))
    (realizedCofan (replacementCellBoundary H)) (realizedCofan (replacementCellBoundary
      pointDiagram))
    (realizedBisimplicialSigmaIsColimit _) (realizedBisimplicialSigmaIsColimit _)
    (stageProjection (replacementPointAugmentation H) n)
    (cellBoundaryProjection (replacementPointAugmentation H) n)
    (attachingLeg H n) (attachingLeg pointDiagram n)
    (cellAttachingSquare (replacementPointAugmentation H) n)
    (fun s ↦ realizationFunctor.map (outerProductCoefficientMap
      (K := (∂Δ[n] : SSet.{u})) ((replacementPointAugmentation H).app (s.1.obj 0))))
    (fun s ↦ realizationFunctor.map (replacementCellAttaching H s))
    (fun s ↦ realizationFunctor.map (replacementCellAttaching pointDiagram s))
    (fun s ↦ componentAttaching_square H s)
  · intro s
    change realizationFunctor.map _ ≫ realizationFunctor.map _ =
      realizationFunctor.map _ ≫ realizationFunctor.map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  · intro s
    change realizationFunctor.map _ ≫ realizationFunctor.map _ = realizationFunctor.map _
    rw [← Functor.map_comp]
    rfl
  · intro s
    change realizationFunctor.map _ ≫ realizationFunctor.map _ = realizationFunctor.map _
    rw [← Functor.map_comp]
    rfl
  · exact componentAttaching_cartesian H htrans n hchart


/-- Both outgoing faces of the genuine successor cube, with both incoming
faces derived from product geometry and finite boundary-chart assembly. -/
theorem replacementSuccessor_cartesian
    (htrans : ∀ ⦃d e : D⦄ (f : d ⟶ e),
      ∃ E : ContinuousMap.HomotopyEquiv |H.obj d| |H.obj e|,
        E.toFun = (SSet.toTop.map (H.map f)).hom)
    (n : ℕ)
    (hchart : ∀ (k : ℕ) (v : (nerve D).obj (op ⦋k⦌))
      (hv : v ∈ ((nerve D).skeleton n).obj (op ⦋k⦌)),
      ChartCartesian H ((nerve D).skeleton n) v hv) :
    Cartesian (stageProjection (replacementPointAugmentation H) n).hom
      (stageProjection (replacementPointAugmentation H) (n+1)).hom
      (stageStep H n).hom (stageStep pointDiagram n).hom
      (congrArg TopCat.Hom.hom (stageStepSquare (replacementPointAugmentation H) n)) ∧
    Cartesian (cellProjection (replacementPointAugmentation H) n).hom
      (stageProjection (replacementPointAugmentation H) (n+1)).hom
      (characteristicLeg H n).hom (characteristicLeg pointDiagram n).hom
      (congrArg TopCat.Hom.hom (cellCharacteristicSquare (replacementPointAugmentation H) n)) :=
  successor_cartesian_of_incoming (replacementPointAugmentation H) n
    (replacementBoundary_cartesian H n) (replacementAttaching_cartesian H htrans n hchart)

end CategoryTheory.TheoremB.Skeletal
