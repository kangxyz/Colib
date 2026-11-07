/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremA.Resolution

/-! Source: `Quillen/CategoryTheory/TheoremA/Grothendieck.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd.
This is a categorical/realized resolution prerequisite, not the general Theorem A criterion. -/

/-!
# Grothendieck presentation of the Theorem A resolution

The covariant diagram `d ↦ (F ↓ d)` and its Grothendieck construction provide
the categorical input to the homotopy-colimit approach to Quillen's Theorem A.
-/
@[expose] public section

noncomputable section

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.TheoremA

variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)

/-- The covariant diagram of comma categories `(F ↓ d)`. -/
def commaDiagram : D ⥤ Cat.{u, u} where
  obj d := Cat.of (CostructuredArrow F d)
  map f := (CostructuredArrow.map f).toCatHom
  map_id d := by
    apply Cat.Hom.ext
    apply CategoryTheory.Functor.ext (fun X ↦ CostructuredArrow.map_id)
  map_comp f g := by
    apply Cat.Hom.ext
    apply CategoryTheory.Functor.ext (fun X ↦ CostructuredArrow.map_comp)

/-- Flatten a Grothendieck object to a resolution object. -/
@[simps]
def flatten : Grothendieck (commaDiagram F) ⥤ Resolution F where
  obj X := ⟨X.fiber.left, X.base, X.fiber.hom⟩
  map f := ⟨f.fiber.left, f.base, CostructuredArrow.w f.fiber⟩
  map_id X := by
    apply Comma.hom_ext
    · simp [commaDiagram, Grothendieck.id_fiber]
    · rfl
  map_comp f g := by
    apply Comma.hom_ext
    · simp [commaDiagram, Grothendieck.comp_fiber]
    · rfl

/-- Display the target of a resolution object as the Grothendieck base. -/
@[simps]
def unflatten : Resolution F ⥤ Grothendieck (commaDiagram F) where
  obj X := ⟨X.right, CostructuredArrow.mk X.hom⟩
  map f := ⟨f.right, CostructuredArrow.homMk f.left f.w⟩
  map_id X := by
    refine Grothendieck.ext _ _ rfl ?_
    apply CostructuredArrow.hom_ext
    simp [commaDiagram, Grothendieck.id_fiber]
  map_comp f g := by
    refine Grothendieck.ext _ _ rfl ?_
    apply CostructuredArrow.hom_ext
    simp [commaDiagram, Grothendieck.comp_fiber]

/-- The Grothendieck presentation of the comma resolution. -/
def grothendieckEquivalence : Grothendieck (commaDiagram F) ≌ Resolution F where
  functor := flatten F
  inverse := unflatten F
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- The presentation respects the projection to the target exactly. -/
@[simp]
theorem flatten_target :
    flatten F ⋙ targetProjection F = Grothendieck.forget (commaDiagram F) := rfl

/-- The inverse presentation also respects the target projection exactly. -/
@[simp]
theorem unflatten_forget :
    unflatten F ⋙ Grothendieck.forget (commaDiagram F) = targetProjection F := rfl

end CategoryTheory.TheoremA
