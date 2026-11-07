/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.ProjectionComma
public import Colib.CategoryTheory.TheoremA.UniverseLift
public import Colib.Topology.ClassifyingSpace.Contraction
public import Colib.Topology.ClassifyingSpace.UniverseHomotopy

/-!
# The actual localization contraction in arbitrary universes

The categorical comma adjunction and the universe-correct Theorem A give a
homotopy equivalence whose forward map is the original projection realization.
-/

@[expose] public section
noncomputable section
universe u v u' v'
open CategoryTheory Topology SSet HomotopyGroup MonoidalCategory
namespace CategoryTheory.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [IsGroupoid C]
  [∀ A : C, (tensorRight A).Faithful]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]

/-- The comma adjunction realizes without replacing either original space. -/
def commaClassifyingHomotopyEquivUniversal (B : C) :
    ContinuousMap.HomotopyEquiv
      (ClassifyingSpace (CostructuredArrow (projection (D := D)) ⟨B⟩))
      (ClassifyingSpace D) :=
  adjunctionClassifyingHomotopyEquivUniversal (commaTransportAdjunction B)

/-- The original projection is a homotopy equivalence for a contractible acted-on space. -/
def projectionClassifyingHomotopyEquivUniversal [ContractibleSpace (ClassifyingSpace D)] :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (Localization C D))
      (ClassifyingSpace (ActionLocalization C C)) :=
  TheoremA.contractibleCommaClassifyingHomotopyEquivUniversal projection
    (fun B ↦ (commaClassifyingHomotopyEquivUniversal B.obj).contractibleSpace)

@[simp]
lemma projectionClassifyingHomotopyEquivUniversal_toFun
    [ContractibleSpace (ClassifyingSpace D)] :
    (projectionClassifyingHomotopyEquivUniversal (C := C) (D := D)).toFun =
      classifyingSpaceMapUniversal projection :=
  TheoremA.contractibleCommaClassifyingHomotopyEquivUniversal_toFun _ _

/-- Contractibility of the actual localization, with arbitrary category universes. -/
theorem classifyingSpace_contractible_universal [ContractibleSpace (ClassifyingSpace D)] :
    ContractibleSpace (ClassifyingSpace (Localization C D)) := by
  let : ContractibleSpace (ClassifyingSpace (ActionLocalization C C)) :=
    classifyingSpace_contractible_of_isInitial
      (ActionLocalization.selfUnitIsInitial (C := C))
  exact (projectionClassifyingHomotopyEquivUniversal (C := C) (D := D)).contractibleSpace

end CategoryTheory.GroupCompletion.Localization
