/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremA.ColumnRealization
public import Colib.CategoryTheory.TheoremA.ReplacementDiagonal
public import Colib.CategoryTheory.TheoremA.Classifying

/-! Source: Quillen/CategoryTheory/TheoremA/Augmentations.lean at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual maps and universal properties retained. -/

/-!
# The two augmentations in the bisimplicial proof of Theorem A

Both augmentations are actual maps. The source augmentation is a realized
homotopy equivalence on every transposed row; the target augmentation has
that property when all comma classifying spaces are contractible. Their
diagonal maps are compared with the canonical map `|N F|` by an actual homotopy.

The step from rowwise equivalences to a diagonal equivalence is deliberately
not asserted here: it is the remaining skeletal realization theorem.
-/
@[expose] public section

noncomputable section

open SSet CategoryTheory Opposite
open scoped Simplicial Topology

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.TheoremA

/-- The diagonal of a constant outer diagram is its value. -/
def diagonalConstantIso (X : SSet.{u}) :
    diagonalSSet ((Functor.const SimplexCategoryᵒᵖ).obj X) ≅ X :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro p q α
    simp [diagonalSSet])

/-- The base nerve viewed as discrete inner rows. -/
def baseBisimplicial (D : Type u) [SmallCategory D] : SimplexCategoryᵒᵖ ⥤ SSet.{u} :=
  nerve D ⋙ Functor.const SimplexCategoryᵒᵖ

/-- The diagonal of the base bisimplicial set is its ordinary nerve. -/
def diagonalBaseIso (D : Type u) [SmallCategory D] :
    diagonalSSet (baseBisimplicial D) ≅ nerve D :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro p q α
    simp [diagonalSSet, baseBisimplicial])

variable {D : Type u} [SmallCategory D]

/-- The replacement of the point diagram is exactly the base bisimplicial set. -/
def replacementPointIso :
    simplicialReplacement ((Functor.const D).obj (Δ[0] : SSet.{u})) ≅
      baseBisimplicial D :=
  NatIso.ofComponents (fun p ↦ pointSigmaIso ((nerve D).obj p)) (by
    intro p q α
    ext r x : 4
    rfl)

/-- The target augmentation at the bisimplicial level. -/
def targetAugmentation (H : D ⥤ SSet.{u}) :
    simplicialReplacement H ⟶ baseBisimplicial D :=
  simplicialReplacementMap (replacementPointAugmentation H) ≫ replacementPointIso.hom

/-- On diagonals the target augmentation is the canonical indexing-chain projection. -/
theorem targetAugmentation_diagonal (H : D ⥤ SSet.{u}) :
    diagonalMap (targetAugmentation H) ≫ (diagonalBaseIso D).hom = replacementBaseMap H := by
  ext p x : 4
  rfl

/-- With contractible diagram values, each target-augmentation row is an
actual homotopy equivalence to its discrete indexing-chain space. -/
def targetRowHomotopyEquiv (H : D ⥤ SSet.{u})
    (h : ∀ d, ContractibleSpace |H.obj d|) (p : SimplexCategoryᵒᵖ) :
    ContinuousMap.HomotopyEquiv |(simplicialReplacement H).obj p|
      |(baseBisimplicial D).obj p| :=
  (contractibleReplacementRowHomotopyEquiv H h p).trans
    (TopCat.homeoOfIso (SSet.toTop.mapIso (replacementPointIso.app p))).toHomotopyEquiv

/-- The target row equivalence has exactly the canonical augmentation map. -/
theorem targetRowHomotopyEquiv_toFun (H : D ⥤ SSet.{u})
    (h : ∀ d, ContractibleSpace |H.obj d|) (p : SimplexCategoryᵒᵖ) :
    (targetRowHomotopyEquiv H h p).toFun =
      (SSet.toTop.map ((targetAugmentation H).app p)).hom := by
  change (SSet.toTop.map (replacementPointIso.app p).hom).hom.comp
    (contractibleReplacementRowHomotopyEquiv H h p).toFun = _
  rw [contractibleReplacementRowHomotopyEquiv_toFun]
  simp only [targetAugmentation, NatTrans.comp_app, Functor.map_comp, TopCat.hom_comp]
  rfl

variable {C : Type u} [SmallCategory C] (F : C ⥤ D)

/-- Forgetting the comma structure gives the source augmentation. -/
def sourceAugmentation :
    simplicialReplacement (commaNerveDiagram F) ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj (nerve C) where
  app p :=
    { app q := ↾fun x ↦ x.2 ⋙ CostructuredArrow.proj F (x.1.obj 0)
      naturality q r α := by
        ext x : 3
        rfl }
  naturality p q α := by
    ext r x : 4
    rfl

/-- Transposing the source augmentation gives the already analyzed column map. -/
theorem sourceAugmentation_column (q : SimplexCategoryᵒᵖ) :
    ((CategoryTheory.flipFunctor _ _ _).map (sourceAugmentation F)).app q =
      commaColumnSourceMap F q := by
  ext p x : 4
  rfl

/-- The source projection on the diagonal homotopy-colimit model. -/
def diagonalSourceMap : replacementDiagonal (commaNerveDiagram F) ⟶ nerve C :=
  diagonalMap (sourceAugmentation F) ≫ (diagonalConstantIso (nerve C)).hom

/-- The source projection agrees with the source projection of the comma resolution. -/
theorem diagonalSourceMap_eq :
    diagonalSourceMap F = commaDiagonalToResolution F ≫ nerveMap (sourceProjection F) := by
  ext p x : 4
  rfl

/-- The two diagonal augmentations compare to the canonical realized functor map. -/
def diagonalAugmentationHomotopy :
    ((classifyingSpaceMap F).hom.comp (SSet.toTop.map (diagonalSourceMap F)).hom).Homotopy
      (SSet.toTop.map (replacementBaseMap (commaNerveDiagram F))).hom :=
  ((comparisonClassifyingHomotopy F).compContinuousMap
    (SSet.toTop.map (commaDiagonalToResolution F)).hom).cast
    (by
      rw [diagonalSourceMap_eq, Functor.map_comp, TopCat.hom_comp]
      rfl)
    (by
      rw [← TopCat.hom_comp]
      change (SSet.toTop.map (commaDiagonalToResolution F) ≫
        SSet.toTop.map (nerveMap (targetProjection F))).hom = _
      rw [← Functor.map_comp, commaDiagonalToResolution_target])

end CategoryTheory.TheoremA
