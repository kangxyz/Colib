/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Comma.AsSmall
public import Colib.Topology.ClassifyingSpace.UniverseLift

/-! # Universe lifting of the original comma classifying spaces

The strict categorical lifts realize to homeomorphisms, retaining every original
comma arrow. Implementation source: `Quillen/CategoryTheory/Comma/UniverseLift.lean`
and `StructuredUniverseLift.lean` at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u₁ v₁ u₂ v₂ w
namespace CategoryTheory
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- Original comma classifying spaces are homeomorphic to their lifted counterparts. -/
def costructuredArrowUniverseHomeomorph (F : C ⥤ D) (d : D) :
    ClassifyingSpace (CostructuredArrow F d) ≃ₜ
      ClassifyingSpace (CostructuredArrow
        ((AsSmall.down : AsSmall.{w} C ⥤ C) ⋙ F ⋙
          (AsSmall.up : D ⥤ AsSmall.{w} D)) (AsSmall.up.obj d)) where
  toFun := classifyingSpaceMapUniversal (CostructuredArrow.asSmallUp F d)
  invFun := classifyingSpaceMapUniversal (CostructuredArrow.asSmallDown F d)
  left_inv x := by
    change ((classifyingSpaceMapUniversal (CostructuredArrow.asSmallDown F d)).comp
      (classifyingSpaceMapUniversal (CostructuredArrow.asSmallUp F d))) x = x
    rw [← classifyingSpaceMapUniversal_comp, CostructuredArrow.asSmallUp_down,
      classifyingSpaceMapUniversal_id]
    rfl
  right_inv x := by
    change ((classifyingSpaceMapUniversal (CostructuredArrow.asSmallUp F d)).comp
      (classifyingSpaceMapUniversal (CostructuredArrow.asSmallDown F d))) x = x
    rw [← classifyingSpaceMapUniversal_comp, CostructuredArrow.asSmallDown_up,
      classifyingSpaceMapUniversal_id]
    rfl
  continuous_toFun := (classifyingSpaceMapUniversal (CostructuredArrow.asSmallUp F d)).continuous
  continuous_invFun := (classifyingSpaceMapUniversal (CostructuredArrow.asSmallDown F d)).continuous

/-- The structured comma lift is a homeomorphism of the original realizations. -/
def structuredArrowUniverseHomeomorph (F : C ⥤ D) (d : D) :
    ClassifyingSpace (StructuredArrow d F) ≃ₜ
      ClassifyingSpace (StructuredArrow (AsSmall.up.obj d)
        ((AsSmall.down : AsSmall.{w} C ⥤ C) ⋙ F ⋙
          (AsSmall.up : D ⥤ AsSmall.{w} D))) where
  toFun := classifyingSpaceMapUniversal (StructuredArrow.asSmallUp F d)
  invFun := classifyingSpaceMapUniversal (StructuredArrow.asSmallDown F d)
  left_inv x := by
    change ((classifyingSpaceMapUniversal (StructuredArrow.asSmallDown F d)).comp
      (classifyingSpaceMapUniversal (StructuredArrow.asSmallUp F d))) x = x
    rw [← classifyingSpaceMapUniversal_comp, StructuredArrow.asSmallUp_down,
      classifyingSpaceMapUniversal_id]
    rfl
  right_inv x := by
    change ((classifyingSpaceMapUniversal (StructuredArrow.asSmallUp F d)).comp
      (classifyingSpaceMapUniversal (StructuredArrow.asSmallDown F d))) x = x
    rw [← classifyingSpaceMapUniversal_comp, StructuredArrow.asSmallDown_up,
      classifyingSpaceMapUniversal_id]
    rfl
  continuous_toFun := (classifyingSpaceMapUniversal (StructuredArrow.asSmallUp F d)).continuous
  continuous_invFun := (classifyingSpaceMapUniversal (StructuredArrow.asSmallDown F d)).continuous

end CategoryTheory
