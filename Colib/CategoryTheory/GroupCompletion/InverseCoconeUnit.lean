/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.CategoryTheory.GroupCompletion.FirstCoordinateAssociativity
public import Colib.CategoryTheory.GroupCompletion.Translation
public import Colib.CategoryTheory.GroupCompletion.FixedFirstEntry
public import Colib.CategoryTheory.GroupCompletion.UnitEntry
public import Colib.CategoryTheory.GroupCompletion.ActionTranslationNaturality

/-!
Adapted from `Quillen/CategoryTheory/GroupCompletion/InverseCoconeUnit.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`; original functors and arrows retained.

# The unit-entry successor of the inverse completed cocone -/
@[expose] public section
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
universe u v
namespace CategoryTheory.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section Unit
variable {D : Type u} [Category.{v} D] [MonoidalLeftAction C D]
/-- The original left unitor identifies the unit-entry inverse stage. -/
def unitFirstCoordinateHom (p : C) :
    unitEntry (C := C) (D := D) ⋙ firstCoordinateTranslation p ⟶ fixedFirstEntry (D := D) p where
  app X := ActionLocalization.ofHom (C := C) (X := (𝟙_ C ⊗ p, X)) (Y := (p, X))
    ((λ_ p).hom, 𝟙 X)
  naturality {X Y} f := by
    dsimp only [Functor.comp_map, unitEntry, fixedFirstEntry]
    erw [ActionLocalization.mapFunctor_ofHom, ← ActionLocalization.ofHom_comp,
      ← ActionLocalization.ofHom_comp]
    congr 1
    apply Prod.ext
    · change (𝟙 (𝟙_ C)) ▷ p ≫ (λ_ p).hom = (λ_ p).hom ≫ 𝟙 p
      simp only [id_whiskerRight, Category.id_comp, Category.comp_id]
    · change f ≫ 𝟙 Y = 𝟙 X ≫ f
      simp only [Category.id_comp, Category.comp_id]
end Unit

/-- The actual diagonal coevaluation and associator restrict along the unit
entry to the prescribed completion successor, with its left unitor. -/
theorem inverseCocone_unit_successor (e p X : C) :
    (firstCoordinateTranslation p).map
      (mkHom (X := (𝟙_ C, X)) (Y := (𝟙_ C ⊗ e, X ⊗ e)) e
        (β_ e (𝟙_ C)).hom (β_ e X).hom) ≫
      ActionLocalization.ofHom (C := C)
        (X := ((𝟙_ C ⊗ e) ⊗ p, X ⊗ e)) (Y := (𝟙_ C ⊗ (e ⊗ p), X ⊗ e))
        ((α_ (𝟙_ C) e p).hom, 𝟙 (X ⊗ e)) ≫
      ActionLocalization.ofHom (C := C)
        (X := (𝟙_ C ⊗ (e ⊗ p), X ⊗ e)) (Y := (e ⊗ p, X ⊗ e))
        ((λ_ (e ⊗ p)).hom, 𝟙 (X ⊗ e)) =
    ActionLocalization.ofHom (C := C) (X := (𝟙_ C ⊗ p, X)) (Y := (p, X))
      ((λ_ p).hom, 𝟙 X) ≫
      ActionLocalization.translation e (p, X) ≫
      ActionLocalization.ofHom (C := C) (X := (e ⊗ p, e ⊗ X)) (Y := (e ⊗ p, X ⊗ e))
        (𝟙 (e ⊗ p), (β_ e X).hom) := by
  rw [firstCoordinateTranslation_mkHom, ← ActionLocalization.ofHom_comp]
  erw [ActionLocalization.mkHom_comp_ofHom]
  conv_rhs => rw [← Category.assoc]
  erw [ActionLocalization.ofHom_translation]
  rw [Category.assoc, ← ActionLocalization.ofHom_comp]
  erw [← ActionLocalization.mkHom_factorization
    (⟨e, (e ◁ (λ_ p).hom ≫ 𝟙 _, e ◁ 𝟙 X ≫ (β_ e X).hom)⟩ :
      ActionLocalization.HomRep (C := C) (𝟙_ C ⊗ p, X) (e ⊗ p, X ⊗ e))]
  apply congrArg ActionLocalization.mkHom
  apply congrArg (ActionLocalization.HomRep.mk e)
  apply Prod.ext
  · change ((α_ e (𝟙_ C) p).inv ≫ (β_ e (𝟙_ C)).hom ▷ p) ≫
        ((α_ (𝟙_ C) e p).hom ≫ (λ_ (e ⊗ p)).hom) =
      e ◁ (λ_ p).hom ≫ 𝟙 _
    rw [leftUnitor_tensor_hom, Iso.hom_inv_id_assoc]
    rw [Category.assoc, ← comp_whiskerRight, braiding_leftUnitor]
    simp only [Category.comp_id, triangle_assoc_comp_right]
  · change (β_ e X).hom ≫ 𝟙 _ ≫ 𝟙 _ = e ◁ 𝟙 X ≫ (β_ e X).hom
    simp only [Category.comp_id, whiskerLeft_id, Category.id_comp]

end CategoryTheory.GroupCompletion.Localization
