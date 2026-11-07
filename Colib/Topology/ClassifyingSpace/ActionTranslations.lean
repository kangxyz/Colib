/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.CategoryTheory.GroupCompletion.ActionTranslations
public import Colib.Topology.ClassifyingSpace.UniverseHomotopy

/-! # Invertible translations of a localized action category -/
@[expose] public section
noncomputable section
universe u v u' v'
open CategoryTheory Topology SSet HomotopyGroup MonoidalCategory
open scoped MonoidalLeftAction
namespace CategoryTheory.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]

/-- The first-coordinate translation has the actual acted-on translation as
homotopy inverse. Both inverse homotopies realize common-denominator arrows. -/
def actionTranslationClassifyingHomotopyEquiv (s : C) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (Localization C D))
      (ClassifyingSpace (Localization C D)) where
  toFun := classifyingSpaceMapUniversal (firstCoordinateTranslation s)
  invFun := classifyingSpaceMapUniversal (secondActionTranslation s)
  left_inv := ⟨(classifyingSpaceUniversalHomotopy (actionDiagonalTranslation s)).symm.cast
    (classifyingSpaceMapUniversal_comp _ _) classifyingSpaceMapUniversal_id⟩
  right_inv := ⟨(classifyingSpaceUniversalHomotopy
    (actionDiagonalTranslationReverse s)).symm.cast
      (classifyingSpaceMapUniversal_comp _ _) classifyingSpaceMapUniversal_id⟩

@[simp]
lemma actionTranslationClassifyingHomotopyEquiv_toFun (s : C) :
    (actionTranslationClassifyingHomotopyEquiv (D := D) s).toFun =
      classifyingSpaceMapUniversal (firstCoordinateTranslation s) := rfl

@[simp]
lemma actionTranslationClassifyingHomotopyEquiv_invFun (s : C) :
    (actionTranslationClassifyingHomotopyEquiv (D := D) s).invFun =
      classifyingSpaceMapUniversal (secondActionTranslation s) := rfl

end CategoryTheory.GroupCompletion.Localization
