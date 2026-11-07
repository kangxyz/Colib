/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremB.StructuredTransport
public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalence

/-! All-degree weak comparison transport at the actual identity-arrow
basepoint. This is a transport theorem; realization remains a separate input. -/
/-! Implementation source: `Quillen/CategoryTheory/TheoremB/StructuredWeakTransport.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual maps, paths and identity
basepoints are retained under native namespace and dependency ownership. -/
@[expose] public section

noncomputable section
universe u
open SSet TopCat Topology CategoryTheory Opposite
namespace CategoryTheory.TheoremB
variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)

@[simp] theorem structuredCommaOppositeEquiv_identity (c : C) :
    (structuredCommaOppositeEquiv F (F.obj c)).toFun
      (classifyingSpacePoint (StructuredArrow.mk (𝟙 (F.obj c)))) =
      classifyingSpacePoint (CostructuredArrow.mk (𝟙 (F.op.obj (op c)))) := by
  have hi : (classifyingOppositeIso (StructuredArrow (F.obj c) F)).inv
      (classifyingSpacePoint (StructuredArrow.mk (𝟙 (F.obj c)))) =
      classifyingSpacePoint (op (StructuredArrow.mk (𝟙 (F.obj c)))) := by
    apply (TopCat.homeoOfIso (classifyingOppositeIso (StructuredArrow (F.obj c) F))).injective
    change (classifyingOppositeIso (StructuredArrow (F.obj c) F)).hom
      ((classifyingOppositeIso (StructuredArrow (F.obj c) F)).inv _) = _
    rw [Iso.inv_hom_id_apply]
    exact (classifyingOppositeIso_point (StructuredArrow.mk (𝟙 (F.obj c)))).symm
  change classifyingSpaceMap (structuredArrowOpEquivalence F (F.obj c)).functor
    ((classifyingOppositeIso (StructuredArrow (F.obj c) F)).inv _) = _
  rw [hi, classifyingSpaceMap_point]
  rfl

/-- The opposite-fiber comparison preserves the basepoint in opposite-object normal form. -/
@[simp]
theorem oppositeFiberHomeomorph_basepoint_op (c : C) :
    oppositeFiberHomeomorph F (F.obj c)
      (HomotopyFiber.basepoint (classifyingSpaceMap F.op).hom
        (classifyingSpacePoint (op (F.obj c))) (classifyingSpacePoint (op c))
        (classifyingSpaceMap_point F.op (op c))) =
      HomotopyFiber.basepoint (classifyingSpaceMap F).hom
        (classifyingSpacePoint (F.obj c)) (classifyingSpacePoint c)
        (classifyingSpaceMap_point F c) := by
  apply Subtype.ext
  apply Prod.ext
  · exact classifyingOppositeIso_point c
  · apply ContinuousMap.ext
    intro t
    rw [oppositeFiberHomeomorph_path]
    exact classifyingOppositeIso_point (F.obj c)

/-- All finite homotopy sets of the canonical structured comparison inherit
bijectivity from the opposite costructured identity comparison. -/
theorem structuredFiberComparison_bijective_of_opposite (c : C) (n : ℕ)
    (h : Function.Bijective (HomotopyGroup.map (N := Fin n)
      (fiberComparison F.op (F.op.obj (op c))) (fiberComparison_identity F.op (op c)))) :
    Function.Bijective (HomotopyGroup.map (N := Fin n)
      (structuredFiberComparison F (F.obj c)) (structuredFiberComparison_identity F c)) := by
  let a := structuredCommaOppositeEquiv F (F.obj c)
  let b := (oppositeFiberHomeomorph F (F.obj c)).toHomotopyEquiv
  have ha := homotopyGroupMap_bijective_of_homotopyEquiv a
    (structuredCommaOppositeEquiv_identity F c) n
  have hb := homotopyGroupMap_bijective_of_homotopyEquiv b
    (oppositeFiberHomeomorph_basepoint_op F c) n
  have h₁ := homotopyGroupMap_bijective_comp a.toFun
    (fiberComparison F.op (F.op.obj (op c)))
    (structuredCommaOppositeEquiv_identity F c) (fiberComparison_identity F.op (op c)) n ha h
  have h₂ := homotopyGroupMap_bijective_comp
    ((fiberComparison F.op (F.op.obj (op c))).comp a.toFun) b.toFun
    ((congrArg (fiberComparison F.op (F.op.obj (op c)))
      (structuredCommaOppositeEquiv_identity F c)).trans (fiberComparison_identity F.op (op c)))
    (oppositeFiberHomeomorph_basepoint_op F c) n h₁ hb
  have hp : transportedStructuredFiberComparison F (F.obj c)
      (classifyingSpacePoint (StructuredArrow.mk (𝟙 (F.obj c)))) =
      HomotopyFiber.basepoint (classifyingSpaceMap F).hom
        (classifyingSpacePoint (F.obj c)) (classifyingSpacePoint c)
        (classifyingSpaceMap_point F c) :=
    ((structuredFiberComparisonTransportHomotopy F (F.obj c)).map_zero_left _).symm.trans
      (structuredFiberComparisonTransportHomotopy_identity F c 0)
  apply homotopyGroupMap_bijective_of_based_homotopy hp
    (structuredFiberComparison_identity F c)
    (structuredFiberComparisonTransportHomotopy F (F.obj c))
    (structuredFiberComparisonTransportHomotopy_identity F c) n
  exact h₂

end CategoryTheory.TheoremB
