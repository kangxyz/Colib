/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremA.ContractibleComma
public import Colib.Topology.ClassifyingSpace.CommaOpposite

/-! The structured-comma form of the proved Quillen Theorem A, retaining the
canonical forward map under opposite-category realization. -/
@[expose] public section

noncomputable section
universe u
open CategoryTheory Opposite
namespace CategoryTheory.TheoremA
variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)

/-- Quillen A in its dual, structured-comma orientation. -/
def contractibleStructuredClassifyingHomotopyEquiv
    (h : ∀ d : D, ContractibleSpace (ClassifyingSpace (StructuredArrow d F))) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace C) (ClassifyingSpace D) := by
  have hop (d : Dᵒᵖ) : ContractibleSpace (ClassifyingSpace (CostructuredArrow F.op d)) := by
    let := h d.unop
    exact (CategoryTheory.structuredCommaOppositeEquiv F d.unop).symm.contractibleSpace
  let e := (TopCat.homeoOfIso (classifyingOppositeIso C)).symm.toHomotopyEquiv.trans
    ((contractibleCommaClassifyingHomotopyEquiv F.op hop).trans
      (TopCat.homeoOfIso (classifyingOppositeIso D)).toHomotopyEquiv)
  have he : e.toFun = (classifyingSpaceMap F).hom := by
    ext x
    change ((classifyingOppositeIso C).inv ≫ classifyingSpaceMap F.op ≫
      (classifyingOppositeIso D).hom) x = (classifyingSpaceMap F) x
    rw [classifyingOppositeIso_naturality]
    simp
  exact { e with
    toFun := (classifyingSpaceMap F).hom
    left_inv := by simpa only [he] using e.left_inv
    right_inv := by simpa only [he] using e.right_inv }

@[simp] theorem contractibleStructuredClassifyingHomotopyEquiv_toFun
    (h : ∀ d : D, ContractibleSpace (ClassifyingSpace (StructuredArrow d F))) :
    (contractibleStructuredClassifyingHomotopyEquiv F h).toFun =
      (classifyingSpaceMap F).hom := rfl

/-- The structured-comma form transfers contractibility from the target. -/
theorem contractibleSpace_of_structured_comma
    (h : ∀ d : D, ContractibleSpace (ClassifyingSpace (StructuredArrow d F)))
    [ContractibleSpace (ClassifyingSpace D)] : ContractibleSpace (ClassifyingSpace C) :=
  (contractibleStructuredClassifyingHomotopyEquiv F h).contractibleSpace

end CategoryTheory.TheoremA

attribute [colib_tag "COL-0232",
  colib_ref "WeibelKBook" "IV, 3.7, page 30" "clause"
    "Quillen Theorem A with its actual map"]
  CategoryTheory.TheoremA.contractibleStructuredClassifyingHomotopyEquiv
