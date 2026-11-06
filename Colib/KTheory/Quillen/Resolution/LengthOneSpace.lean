/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module
public import Colib.CategoryTheory.TheoremA.ContractibleStructured
public import Colib.CategoryTheory.ExactCategory.Resolution.CommaContraction
public import Colib.KTheory.Quillen.Basic

/-!
# Actual length-one Q-inclusion equivalence

Extracted from Quillen/Resolution/{FullQ,InheritedQ,LengthOne}.lean at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Theorem A is now a proved input,
not an assumption. This file stops at the actual Q-classifying-space equivalence;
chosen-zero normalization and the canonical all-degree K-map are separate.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ExactCategory.Resolution
variable {C : Type u} [SmallCategory C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) (P : ObjectProperty C)
section Full
variable [E.IsAdmissibleSubobjectClosed P] [E.IsExtensionClosed P]

/-- The full ambient Q-subcategory is homotopy equivalent to ambient Q under
admissible-subobject closure and actual admissible epimorphic covers. -/
def fullQClassifyingHomotopyEquiv (h : ∀ M, Nonempty (Cover E P M)) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (FullQ E P)) E.KSpace :=
  TheoremA.contractibleStructuredClassifyingHomotopyEquiv (fullQInclusion E P)
    (fun M => fullQComma_contractible E P M.obj.of (Classical.choice (h M.obj.of)))

@[simp] theorem fullQClassifyingHomotopyEquiv_toFun
    (h : ∀ M, Nonempty (Cover E P M)) :
    (fullQClassifyingHomotopyEquiv E P h).toFun =
      (classifyingSpaceMap (fullQInclusion E P)).hom := rfl

end Full
variable [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [E.IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
section Strong
variable [E.IsAdmissibleSubobjectClosed P]

/-- The inherited Q-construction and the larger full ambient Q-subcategory
have homotopy equivalent classifying spaces, by the actual span reflection. -/
def inheritedQClassifyingHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (ExactSubcategory.exactStructure E P).KSpace
      (ClassifyingSpace (FullQ E P)) :=
  TheoremA.contractibleCommaClassifyingHomotopyEquiv (inheritedToFullQ E P)
    (inheritedComma_contractible E P)

@[simp] theorem inheritedQClassifyingHomotopyEquiv_toFun :
    (inheritedQClassifyingHomotopyEquiv E P).toFun =
      (classifyingSpaceMap (inheritedToFullQ E P)).hom := rfl

/-- Resolution under admissible-subobject closure and actual covers. -/
def classifyingHomotopyEquivOfCovers (h : ∀ M, Nonempty (Cover E P M)) :
    ContinuousMap.HomotopyEquiv (ExactSubcategory.exactStructure E P).KSpace E.KSpace :=
  (inheritedQClassifyingHomotopyEquiv E P).trans (fullQClassifyingHomotopyEquiv E P h)

/-- The resulting forward map is exactly the original Q-inclusion. -/
@[simp] theorem classifyingHomotopyEquivOfCovers_toFun (h : ∀ M, Nonempty (Cover E P M)) :
    (classifyingHomotopyEquivOfCovers E P h).toFun =
      (classifyingSpaceMap (exactInclusion E P).mapQ).hom := by
  change (classifyingSpaceMap (fullQInclusion E P)).hom.comp
    (classifyingSpaceMap (inheritedToFullQ E P)).hom = _
  rw [← TopCat.hom_comp, ← classifyingSpaceMap_comp, inheritedToFullQ_comp]

end Strong
variable [E.IsKernelClosed P]

/-- Quillen's length-one resolution theorem on actual Q-classifying spaces. -/
def classifyingHomotopyEquivOfLengthOne (h : ∀ X, E.ResolutionLength P 1 X) :
    ContinuousMap.HomotopyEquiv (ExactSubcategory.exactStructure E P).KSpace E.KSpace := by
  letI := E.admissibleSubobjectClosed_of_resolutionLength_one P h
  exact classifyingHomotopyEquivOfCovers E P (fun X => by
    obtain ⟨R, _⟩ := h X
    obtain ⟨Y, p, hY, hp⟩ := R.presentation
    exact ⟨⟨Y, hY, p, hp⟩⟩)

@[simp] theorem classifyingHomotopyEquivOfLengthOne_toFun
    (h : ∀ X, E.ResolutionLength P 1 X) :
    (classifyingHomotopyEquivOfLengthOne E P h).toFun =
      (classifyingSpaceMap (exactInclusion E P).mapQ).hom := by
  let := E.admissibleSubobjectClosed_of_resolutionLength_one P h
  exact classifyingHomotopyEquivOfCovers_toFun E P _

end CategoryTheory.ExactCategory.Resolution
