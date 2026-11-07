/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremA.Grothendieck
public import Colib.CategoryTheory.TheoremA.StructuredResolution
public import Colib.Topology.Realization.HomotopyBridge

/-! Source: `Quillen/CategoryTheory/TheoremA/Classifying.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd.
This is a categorical/realized resolution prerequisite, not the general Theorem A criterion. -/

/-!
# Realized deformation retractions for the Theorem A resolutions

Both comma resolutions have actual classifying spaces homotopy equivalent to
the source category, via the canonical source projection. Their target maps
are compared to the map induced by `F` by genuine continuous homotopies.

No contractible-fiber implication for the target projection is assumed or
proved here. That implication requires the remaining homotopy-colimit theorem.
-/
@[expose] public section

noncomputable section

open CategoryTheory
open scoped Topology unitInterval

universe u

namespace CategoryTheory.TheoremA

variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)

/-- The comma resolution retracts onto the source category after realization.
Its forward map is exactly the realized source projection. -/
def sourceClassifyingHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (Resolution F)) (ClassifyingSpace C) :=
  (adjunctionClassifyingHomotopyEquiv (sectionAdjunction F)).symm

@[simp]
theorem sourceClassifyingHomotopyEquiv_apply (x : ClassifyingSpace (Resolution F)) :
    sourceClassifyingHomotopyEquiv F x = classifyingSpaceMap (sourceProjection F) x := rfl

@[simp]
theorem sourceClassifyingHomotopyEquiv_symm_apply (x : ClassifyingSpace C) :
    (sourceClassifyingHomotopyEquiv F).symm x = classifyingSpaceMap (sectionFunctor F) x := rfl

/-- The actual continuous comparison between the resolved map and `|N F|`. -/
def comparisonClassifyingHomotopy :
    ((classifyingSpaceMap F).hom.comp (classifyingSpaceMap (sourceProjection F)).hom).Homotopy
      (classifyingSpaceMap (targetProjection F)).hom :=
  (classifyingSpaceNaturalTransformationHomotopy (comparison F)).cast
    (by simp only [classifyingSpaceMap_comp, TopCat.hom_comp]) rfl

/-- The original map factors strictly through the identity-arrow section and
the target projection, preserving the canonical map in the eventual theorem. -/
@[simp]
theorem section_target_classifying :
    classifyingSpaceMap (sectionFunctor F) ≫ classifyingSpaceMap (targetProjection F) =
      classifyingSpaceMap F := by
  rw [← classifyingSpaceMap_comp, section_target]

/-- The Grothendieck presentation induces a genuine homotopy equivalence. -/
def grothendieckClassifyingHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (Grothendieck (commaDiagram F)))
      (ClassifyingSpace (Resolution F)) :=
  equivalenceClassifyingHomotopyEquiv (grothendieckEquivalence F)

/-- The homotopy contracting the resolution is fixed at every section vertex. -/
def contractionClassifyingBasedHomotopy (c : C) :
    (classifyingSpaceMap (sourceProjection F ⋙ sectionFunctor F)).hom.HomotopyRel
      (classifyingSpaceMap (𝟭 (Resolution F))).hom
      {classifyingSpacePoint ((sectionFunctor F).obj c)} :=
  classifyingSpaceNaturalTransformationBasedHomotopy (contraction F)
    ((sectionFunctor F).obj c) rfl rfl

namespace Structured

/-- The structured-arrow resolution also retracts onto `C`, using the other
adjunction orientation. Its forward map remains the source projection. -/
def sourceClassifyingHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (Resolution F)) (ClassifyingSpace C) :=
  adjunctionClassifyingHomotopyEquiv (sectionAdjunction F)

@[simp]
theorem sourceClassifyingHomotopyEquiv_apply (x : ClassifyingSpace (Resolution F)) :
    sourceClassifyingHomotopyEquiv F x = classifyingSpaceMap (sourceProjection F) x := rfl

/-- In this orientation the structure-arrow homotopy runs in the reverse direction. -/
def comparisonClassifyingHomotopy :
    (classifyingSpaceMap (targetProjection F)).hom.Homotopy
      ((classifyingSpaceMap F).hom.comp (classifyingSpaceMap (sourceProjection F)).hom) :=
  (classifyingSpaceNaturalTransformationHomotopy (comparison F)).cast rfl
    (by simp only [classifyingSpaceMap_comp, TopCat.hom_comp])

@[simp]
theorem section_target_classifying :
    classifyingSpaceMap (sectionFunctor F) ≫ classifyingSpaceMap (targetProjection F) =
      classifyingSpaceMap F := by
  rw [← classifyingSpaceMap_comp, section_target]

end Structured

end CategoryTheory.TheoremA
