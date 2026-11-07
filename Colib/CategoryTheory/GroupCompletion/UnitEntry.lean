/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.ProjectionComma

/-!
Implementation provenance:
`Quillen/CategoryTheory/GroupCompletion/UnitEntry.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # The actual unit entry of action localization -/
@[expose] public section
noncomputable section
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
universe u v u' v'
namespace CategoryTheory.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]

/-- The original acted-on object, with unit denominator in the localized category. -/
def unitEntry : D ⥤ Localization C D where
  obj X := ⟨(𝟙_ C, X)⟩
  map f := ActionLocalization.ofHom (𝟙 (𝟙_ C), f)
  map_id X := ActionLocalization.ofHom_id _
  map_comp {X Y Z} f g := by
    simpa using ActionLocalization.ofHom_comp (C := C)
      (X := (𝟙_ C, X)) (Y := (𝟙_ C, Y)) (Z := (𝟙_ C, Z))
      (𝟙 (𝟙_ C), f) (𝟙 (𝟙_ C), g)

/-- The entry is exactly the comma-entry projection whenever that adjunction is available. -/
theorem unitEntry_eq_comma :
    unitEntry (C := C) (D := D) = commaEntry (𝟙_ C) ⋙
      CostructuredArrow.proj (projection (C := C) (D := D)) ⟨𝟙_ C⟩ := rfl

end CategoryTheory.GroupCompletion.Localization
