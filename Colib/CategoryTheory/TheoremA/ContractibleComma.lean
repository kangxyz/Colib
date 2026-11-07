/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremA.ReplacementInvariance
public import Colib.CategoryTheory.TheoremA.ColumnOpposite
public import Colib.CategoryTheory.TheoremA.OuterOppositeRealization
public import Colib.CategoryTheory.TheoremA.Conclusion
public import Colib.Topology.Homotopy.Equiv.IsoSquare

/-! Source: Quillen/CategoryTheory/TheoremA/ContractibleComma.lean at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Native topology lower owners are reused. -/

/-! # Quillen's Theorem A from contractible comma classifying spaces -/
@[expose] public section

noncomputable section

open SSet TopCat CategoryTheory Limits Opposite
open scoped Simplicial Topology

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.TheoremA

variable {D : Type u} [SmallCategory D]

/-- The target augmentation is an actual homotopy equivalence when its
coefficient realizations are contractible. -/
def targetAugmentationRealizationHomotopyEquiv (H : D ⥤ SSet.{u})
    (h : ∀ d, ContractibleSpace |H.obj d|) :
    ContinuousMap.HomotopyEquiv |diagonalSSet (simplicialReplacement H)|
      |diagonalSSet (baseBisimplicial D)| :=
  homotopyEquivOfIsoSquare (SSet.toTop.map (diagonalMap (targetAugmentation H)))
    (SSet.toTop.map (replacementBaseMap H)) (Iso.refl _)
    (SSet.toTop.mapIso (diagonalBaseIso D))
    (by simpa only [Functor.mapIso_hom, Iso.refl_hom, Category.id_comp, Functor.map_comp]
      using congrArg SSet.toTop.map (targetAugmentation_diagonal H))
    (contractibleReplacementRealizationHomotopyEquiv H h)
    (contractibleReplacementRealizationHomotopyEquiv_toFun H h)

@[simp]
theorem targetAugmentationRealizationHomotopyEquiv_toFun (H : D ⥤ SSet.{u})
    (h : ∀ d, ContractibleSpace |H.obj d|) :
    (targetAugmentationRealizationHomotopyEquiv H h).toFun =
      (SSet.toTop.map (diagonalMap (targetAugmentation H))).hom := rfl

/-- Flipping and then reversing the outer coordinate changes realization
by an actual natural homeomorphism. -/
def flippedOuterOppositeRealizationIso (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    |diagonalSSet (SimplexCategory.rev.op ⋙ X.flip)| ≅ |diagonalSSet X| :=
  outerOppositeRealizationIso X.flip ≪≫ SSet.toTop.mapIso (diagonalFlipIso X)

/-- The flipped outer-reversal comparison preserves the prescribed map. -/
theorem flippedOuterOppositeRealizationIso_naturality
    {X Y : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (η : X ⟶ Y) :
    SSet.toTop.map (diagonalMap (Functor.whiskerLeft SimplexCategory.rev.op
        ((CategoryTheory.flipFunctor _ _ _).map η))) ≫
        (flippedOuterOppositeRealizationIso Y).hom =
      (flippedOuterOppositeRealizationIso X).hom ≫ SSet.toTop.map (diagonalMap η) := by
  have h₁ := outerOppositeRealizationIso_naturality ((CategoryTheory.flipFunctor _ _ _).map η)
  have h₂ := congrArg SSet.toTop.map (diagonalFlipIso_naturality η)
  simp only [Functor.map_comp] at h₂
  exact ((CommSq.mk h₁).vert_comp (CommSq.mk h₂)).w

variable {C : Type u} [SmallCategory C] (F : C ⥤ D)

/-- The opposite-column identification and the genuine replacement theorem
prove an equivalence for the reversed transposed source augmentation. -/
def reversedSourceAugmentationHomotopyEquiv :
    ContinuousMap.HomotopyEquiv
      |diagonalSSet (SimplexCategory.rev.op ⋙ (simplicialReplacement (commaNerveDiagram F)).flip)|
      |diagonalSSet (SimplexCategory.rev.op ⋙
        ((Functor.const SimplexCategoryᵒᵖ).obj (nerve C)).flip)| :=
  homotopyEquivOfIsoSquare
    (SSet.toTop.map (diagonalMap (Functor.whiskerLeft SimplexCategory.rev.op
      ((CategoryTheory.flipFunctor _ _ _).map (sourceAugmentation F)))))
    (SSet.toTop.map (diagonalMap (targetAugmentation (sourceUnderNerveDiagram F))))
    ((diagonalFunctor ⋙ SSet.toTop).mapIso (sourceColumnsOppositeIso F))
    ((diagonalFunctor ⋙ SSet.toTop).mapIso sourceBaseOppositeIso)
    (by
      change (diagonalFunctor ⋙ SSet.toTop).map
          (Functor.whiskerLeft SimplexCategory.rev.op
            ((CategoryTheory.flipFunctor _ _ _).map (sourceAugmentation F))) ≫
        (diagonalFunctor ⋙ SSet.toTop).map sourceBaseOppositeIso.hom =
          (diagonalFunctor ⋙ SSet.toTop).map (sourceColumnsOppositeIso F).hom ≫
        (diagonalFunctor ⋙ SSet.toTop).map (targetAugmentation (sourceUnderNerveDiagram F))
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg (diagonalFunctor ⋙ SSet.toTop).map (sourceColumnsOppositeIso_augmentation F))
    (targetAugmentationRealizationHomotopyEquiv (sourceUnderNerveDiagram F)
      (sourceUnderNerveDiagram_contractible F)) rfl

@[simp]
theorem reversedSourceAugmentationHomotopyEquiv_toFun :
    (reversedSourceAugmentationHomotopyEquiv F).toFun =
      (SSet.toTop.map (diagonalMap (Functor.whiskerLeft SimplexCategory.rev.op
        ((CategoryTheory.flipFunctor _ _ _).map (sourceAugmentation F))))).hom := rfl

/-- The source augmentation is an actual equivalence on diagonal realization,
with no hypothesis on the original functor. -/
def sourceAugmentationRealizationHomotopyEquiv :
    ContinuousMap.HomotopyEquiv |replacementDiagonal (commaNerveDiagram F)|
      |diagonalSSet ((Functor.const SimplexCategoryᵒᵖ).obj (nerve C))| := by
  let eA := flippedOuterOppositeRealizationIso (simplicialReplacement (commaNerveDiagram F))
  let eB := flippedOuterOppositeRealizationIso ((Functor.const SimplexCategoryᵒᵖ).obj (nerve C))
  refine homotopyEquivOfIsoSquare
    (SSet.toTop.map (diagonalMap (sourceAugmentation F)))
    (SSet.toTop.map (diagonalMap (Functor.whiskerLeft SimplexCategory.rev.op
      ((CategoryTheory.flipFunctor _ _ _).map (sourceAugmentation F)))))
    eA.symm eB.symm ?_ (reversedSourceAugmentationHomotopyEquiv F) rfl
  change SSet.toTop.map (diagonalMap (sourceAugmentation F)) ≫ eB.inv = eA.inv ≫ _
  apply (cancel_mono eB.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hw := flippedOuterOppositeRealizationIso_naturality (sourceAugmentation F)
  change _ ≫ eB.hom = eA.hom ≫ _ at hw
  rw [hw]
  simp

@[simp]
theorem sourceAugmentationRealizationHomotopyEquiv_toFun :
    (sourceAugmentationRealizationHomotopyEquiv F).toFun =
      (SSet.toTop.map (diagonalMap (sourceAugmentation F))).hom := rfl

/-- The full diagonal source projection is a homotopy equivalence. -/
def diagonalSourceHomotopyEquiv :
    ContinuousMap.HomotopyEquiv |replacementDiagonal (commaNerveDiagram F)| (ClassifyingSpace C) :=
  (sourceAugmentationRealizationHomotopyEquiv F).trans
    (TopCat.homeoOfIso (SSet.toTop.mapIso (diagonalConstantIso (nerve C)))).toHomotopyEquiv

@[simp]
theorem diagonalSourceHomotopyEquiv_toFun :
    (diagonalSourceHomotopyEquiv F).toFun =
      (SSet.toTop.map (diagonalSourceMap F)).hom := by
  change (SSet.toTop.map (diagonalConstantIso (nerve C)).hom).hom.comp
    (sourceAugmentationRealizationHomotopyEquiv F).toFun = _
  rw [sourceAugmentationRealizationHomotopyEquiv_toFun]
  simp only [diagonalSourceMap, Functor.map_comp, TopCat.hom_comp]

/-- Quillen's Theorem A: if every costructured comma category `F / d` has
contractible classifying space, the actual classifying-space map of `F` is a
homotopy equivalence. The conclusion is constructed, not assumed. -/
def contractibleCommaClassifyingHomotopyEquiv
    (h : ∀ d : D, ContractibleSpace (ClassifyingSpace (CostructuredArrow F d))) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace C) (ClassifyingSpace D) :=
  canonicalEquivalenceFromAugmentations F (diagonalSourceHomotopyEquiv F)
    (contractibleReplacementRealizationHomotopyEquiv (commaNerveDiagram F) h)
    (diagonalSourceHomotopyEquiv_toFun F)
    (contractibleReplacementRealizationHomotopyEquiv_toFun (commaNerveDiagram F) h)

/-- The equivalence supplied by Theorem A has exactly `|N F|` as its forward map. -/
@[simp]
theorem contractibleCommaClassifyingHomotopyEquiv_toFun
    (h : ∀ d : D, ContractibleSpace (ClassifyingSpace (CostructuredArrow F d))) :
    (contractibleCommaClassifyingHomotopyEquiv F h).toFun = (classifyingSpaceMap F).hom := rfl

end CategoryTheory.TheoremA

attribute [colib_tag "COL-0232",
  colib_ref "WeibelKBook" "IV, 3.7, page 30" "clause"
    "Quillen Theorem A with its actual map"]
  CategoryTheory.TheoremA.contractibleCommaClassifyingHomotopyEquiv
