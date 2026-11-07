/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.Translation
public import Colib.Topology.Realization.HomotopyBridge
public import Colib.Topology.ClassifyingSpace.Map
public import Colib.Topology.Homotopy.HomotopyGroup.Map
public import Mathlib.Topology.Homotopy.Equiv

/-!
# Translations of the actual classifying space of `C⁻¹C`

For a braided monoidal category, the two coordinate translations of Grayson's
category induce mutually inverse homotopy equivalences on its classifying
space. The homotopies are obtained by realizing explicit natural transformations.
No homological group-completion assertion is used here.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory Topology SSet HomotopyGroup

namespace CategoryTheory.GroupCompletion.Localization

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- The first-then-second coordinate translation is homotopic to the identity. -/
def firstSecondClassifyingHomotopy (s : C) :
    (ContinuousMap.id (ClassifyingSpace (Localization C C))).Homotopy
      ((classifyingSpaceMap (secondTranslation s)).hom.comp
        (classifyingSpaceMap (firstTranslation s)).hom) := by
  simpa only [classifyingSpaceMap_id, classifyingSpaceMap_comp, TopCat.hom_id,
    TopCat.hom_comp] using
    classifyingSpaceNaturalTransformationHomotopy (firstSecondTranslationNatTrans s)

/-- The second-then-first coordinate translation is homotopic to the identity. -/
def secondFirstClassifyingHomotopy (s : C) :
    (ContinuousMap.id (ClassifyingSpace (Localization C C))).Homotopy
      ((classifyingSpaceMap (firstTranslation s)).hom.comp
        (classifyingSpaceMap (secondTranslation s)).hom) := by
  simpa only [classifyingSpaceMap_id, classifyingSpaceMap_comp, TopCat.hom_id,
    TopCat.hom_comp] using
    classifyingSpaceNaturalTransformationHomotopy (secondFirstTranslationNatTrans s)

/-- Translating the first coordinate of `C⁻¹C` is a homotopy equivalence;
its actual inverse translates the second coordinate by the same object. -/
def translationClassifyingHomotopyEquiv (s : C) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (Localization C C))
      (ClassifyingSpace (Localization C C)) where
  toFun := (classifyingSpaceMap (firstTranslation s)).hom
  invFun := (classifyingSpaceMap (secondTranslation s)).hom
  left_inv := ⟨(firstSecondClassifyingHomotopy s).symm⟩
  right_inv := ⟨(secondFirstClassifyingHomotopy s).symm⟩

@[simp]
lemma translationClassifyingHomotopyEquiv_apply (s : C)
    (x : ClassifyingSpace (Localization C C)) :
    translationClassifyingHomotopyEquiv s x = classifyingSpaceMap (firstTranslation s) x := rfl

@[simp]
lemma translationClassifyingHomotopyEquiv_symm_apply (s : C)
    (x : ClassifyingSpace (Localization C C)) :
    (translationClassifyingHomotopyEquiv s).symm x =
      classifyingSpaceMap (secondTranslation s) x := rfl

end CategoryTheory.GroupCompletion.Localization
