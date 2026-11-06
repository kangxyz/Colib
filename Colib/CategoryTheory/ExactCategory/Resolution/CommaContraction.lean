/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.CategoryTheory.ExactCategory.Resolution.InheritedQ
public import Colib.CategoryTheory.ExactCategory.Resolution.CoverClassifyingSpace
public import Colib.Topology.ClassifyingSpace.Adjunction
public import Colib.Topology.ClassifyingSpace.Opposite

/-!
# Actual Q-comma contractions from span adjunctions

Source: Quillen/Resolution/FullQ.lean and InheritedQ.lean at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The explicit comparison functors,
opposite-category direction, and inherited exact structure are retained.
This supplies actual comma contractions, not a general Theorem A or Resolution K-equivalence.
-/
@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.ExactCategory.Resolution
variable {C : Type u} [SmallCategory C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) (P : ObjectProperty C)

section Full
variable [E.IsAdmissibleSubobjectClosed P]

/-- The actual cover-to-comma adjunction realizes to this homotopy equivalence. -/
def coversCommaHomotopyEquiv (M : C) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (Cover E P M)ᵒᵖ)
      (ClassifyingSpace (FullQComma E P M)) :=
  adjunctionClassifyingHomotopyEquiv (coverAdjunction E P M)

/-- Its forward map is precisely the realized functor sending covers to reverse Q-arrows. -/
theorem coversCommaHomotopyEquiv_toFun (M : C) :
    (coversCommaHomotopyEquiv E P M).toFun =
      (classifyingSpaceMap (coversToComma E P M)).hom := rfl

variable [E.IsExtensionClosed P]

/-- The structured comma is contractible via the actual cover contraction and span adjunction. -/
theorem fullQComma_contractible (M : C) (B : Cover E P M) :
    ContractibleSpace (ClassifyingSpace (FullQComma E P M)) := by
  let := Cover.contractible B
  let : ContractibleSpace (ClassifyingSpace (Cover E P M)ᵒᵖ) :=
    (TopCat.homeoOfIso (classifyingOppositeIso (Cover E P M))).toHomotopyEquiv.contractibleSpace
  exact (coversCommaHomotopyEquiv E P M).symm.contractibleSpace

end Full

/-- Length-one resolutions prove the stronger closure before constructing the actual comma. -/
theorem fullQComma_contractible_of_length_one [P.IsClosedUnderIsomorphisms]
    [E.IsExtensionClosed P] [E.IsKernelClosed P]
    (h : ∀ X, E.ResolutionLength P 1 X) (M : C) :
    ContractibleSpace (ClassifyingSpace (FullQComma E P M)) := by
  let := E.admissibleSubobjectClosed_of_resolutionLength_one P h
  obtain ⟨R, _⟩ := h M
  exact fullQComma_contractible E P M (Cover.ofFiniteResolution R)

section Inherited
variable [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [E.IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts] [E.IsAdmissibleSubobjectClosed P]

/-- The span reflection realizes from the inherited comma to actual admissible subobjects. -/
def subobjectsCommaHomotopyEquiv (B : FullQ E P) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (InheritedComma E P B))
      (ClassifyingSpace (AdmissibleSubobject E P B.obj.obj.of)) :=
  adjunctionClassifyingHomotopyEquiv (subobjectAdjunction E P B)

/-- The inverse is the actual functor from ordinary subobjects into the comma. -/
theorem subobjectsCommaHomotopyEquiv_invFun (B : FullQ E P) :
    (subobjectsCommaHomotopyEquiv E P B).invFun =
      (classifyingSpaceMap (subobjectsToComma E P B)).hom := rfl

/-- The actual initial zero subobject contracts the inherited-Q comma via the reflection. -/
theorem inheritedComma_contractible (B : FullQ E P) :
    ContractibleSpace (ClassifyingSpace (InheritedComma E P B)) := by
  let := classifyingSpace_contractible_of_isInitial
    (AdmissibleSubobject.zeroIsInitial (E := E) (P := P) B.obj.obj.of)
  exact (subobjectsCommaHomotopyEquiv E P B).contractibleSpace

end Inherited

/-- Original length-one hypotheses suffice for the inherited comma, after the proved upgrade. -/
theorem inheritedComma_contractible_of_length_one [P.ContainsZero]
    [P.IsClosedUnderIsomorphisms] [E.IsExtensionClosed P] [P.IsClosedUnderFiniteProducts]
    [E.IsKernelClosed P] (h : ∀ X, E.ResolutionLength P 1 X) (B : FullQ E P) :
    ContractibleSpace (ClassifyingSpace (InheritedComma E P B)) := by
  let := E.admissibleSubobjectClosed_of_resolutionLength_one P h
  exact inheritedComma_contractible E P B

end CategoryTheory.ExactCategory.Resolution

attribute [colib_tag "COL-0235",
  colib_ref "WeibelKBook" "V, proof of Proposition 3.1.1, pages 20-21" "adaptation"
    "Length-one Q comma contractions"]
  CategoryTheory.ExactCategory.Resolution.fullQComma_contractible
  CategoryTheory.ExactCategory.Resolution.inheritedComma_contractible
