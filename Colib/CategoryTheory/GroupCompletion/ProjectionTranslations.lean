/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.CategoryTheory.GroupCompletion.ProjectionComma

/-!
Implementation provenance:
`Quillen/CategoryTheory/GroupCompletion/ProjectionTranslations.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Actual translation squares for the first-coordinate projection -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v'
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
namespace CategoryTheory.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [IsGroupoid C]
  [∀ A : C, (tensorRight A).Faithful]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]

/-- A representative of a base arrow gives the actual natural transport square. -/
def commaTranslation {A B : C} (s : C) (f : s ⊗ A ⟶ B) :
    commaEntry (D := D) A ⋙ CostructuredArrow.map (ActionLocalization.mkHom ⟨s, f⟩) ⟶
      MonoidalLeftAction.actionLeft D s ⋙ commaEntry B where
  app X := CostructuredArrow.homMk
    (mkHom (X := (A, X)) (Y := (B, s ⊙ₗ X)) s f (𝟙 _)) (by
      change projection.map (mkHom (X := (A, X)) (Y := (B, s ⊙ₗ X)) s f (𝟙 _)) ≫
        𝟙 _ = 𝟙 _ ≫ ActionLocalization.mkHom ⟨s, f⟩
      rw [projection_mkHom, Category.comp_id, Category.id_comp])
  naturality {X Y} g := by
    apply CostructuredArrow.hom_ext
    change ActionLocalization.ofHom (X := (A, X)) (Y := (A, Y)) (𝟙 A, g) ≫
      mkHom (X := (A, Y)) (Y := (B, s ⊙ₗ Y)) s f (𝟙 _) =
      mkHom (X := (A, X)) (Y := (B, s ⊙ₗ X)) s f (𝟙 _) ≫
        ActionLocalization.ofHom (X := (B, s ⊙ₗ X)) (Y := (B, s ⊙ₗ Y))
          (𝟙 B, s ⊴ₗ g)
    unfold mkHom
    rw [ActionLocalization.ofHom_comp_mkHom, ActionLocalization.mkHom_comp_ofHom]
    congr 1
    congr 1
    change (s ◁ 𝟙 A ≫ f, s ⊴ₗ g ≫ 𝟙 _) = (f ≫ 𝟙 B, 𝟙 _ ≫ s ⊴ₗ g)
    simp

end CategoryTheory.GroupCompletion.Localization
