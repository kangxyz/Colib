/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.CategoryTheory.GroupCompletion.FirstCoordinateTranslation
public import Colib.CategoryTheory.Monoidal.Action.Braided

/-!
Implementation provenance:
`Quillen/CategoryTheory/GroupCompletion/ActionTranslations.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Inverting translations for an arbitrary acted-on category -/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v'
open CategoryTheory MonoidalCategory BraidedCategory
open scoped MonoidalLeftAction
namespace CategoryTheory.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]

section Braided
variable [BraidedCategory C]

/-- Translate only the acted-on coordinate by the original actor action. -/
def secondActionTensor (s : C) : C × D ⥤ C × D :=
  (𝟭 C).prod (MonoidalLeftAction.actionLeft D s)

instance secondActionTensorLinear (s : C) :
    (secondActionTensor (D := D) s).LaxLeftLinear C where
  μₗ t X := (𝟙 _, MonoidalLeftAction.actionSwap s t X.2)
  μₗ_naturality_left f X := by
    apply Prod.ext
    · change (f ▷ X.1) ≫ 𝟙 _ = 𝟙 _ ≫ (f ▷ X.1)
      simp
    · exact MonoidalLeftAction.actionSwap_naturality_actor s f X.2
  μₗ_naturality_right t _ _ f := by
    apply Prod.ext
    · change (t ◁ f.1) ≫ 𝟙 _ = 𝟙 _ ≫ (t ◁ f.1)
      simp
    · exact MonoidalLeftAction.actionSwap_naturality s t f.2
  μₗ_associativity t r X := by
    apply Prod.ext
    · change 𝟙 _ ≫ (α_ t r X.1).hom = (α_ t r X.1).hom ≫ t ◁ 𝟙 _ ≫ 𝟙 _
      simp
    · exact MonoidalLeftAction.actionSwap_associativity s t r X.2
  μₗ_unitality X := by
    apply Prod.ext
    · change (λ_ X.1).hom = 𝟙 _ ≫ (λ_ X.1).hom
      simp
    · exact MonoidalLeftAction.actionSwap_unitality s X.2

/-- The second action descends through the actual quotient of representatives. -/
def secondActionTranslation (s : C) : Localization C D ⥤ Localization C D :=
  ActionLocalization.mapFunctor (secondActionTensor s)

@[simp]
lemma secondActionTranslation_obj (s : C) (X : Localization C D) :
    (secondActionTranslation s).obj X = ⟨(X.obj.1, s ⊙ₗ X.obj.2)⟩ := rfl

@[simp]
lemma secondActionTranslation_mkHom (s : C) {X Y : C × D} (t : C)
    (f : t ⊗ X.1 ⟶ Y.1) (g : t ⊙ₗ X.2 ⟶ Y.2) :
    (secondActionTranslation s).map (mkHom t f g) =
      mkHom (X := (X.1, s ⊙ₗ X.2)) (Y := (Y.1, s ⊙ₗ Y.2)) t f
        (MonoidalLeftAction.actionSwap s t X.2 ≫ s ⊴ₗ g) := by
  change ActionLocalization.mkHom (X := (X.1, s ⊙ₗ X.2))
    (Y := (Y.1, s ⊙ₗ Y.2)) ⟨t, (𝟙 _ ≫ f, _)⟩ = _
  rw [Category.id_comp]
  rfl

/-- The translations on the separate coordinates commute as actual functors. -/
lemma firstCoordinateTranslation_comp_secondAction (s t : C) :
    firstCoordinateTranslation (D := D) s ⋙ secondActionTranslation t =
      secondActionTranslation t ⋙ firstCoordinateTranslation s := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro X Y f
  change (secondActionTranslation t).map ((firstCoordinateTranslation s).map f) =
    𝟙 _ ≫ (firstCoordinateTranslation s).map ((secondActionTranslation t).map f) ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]
  obtain ⟨r, rfl⟩ := ActionLocalization.mkHom_surjective X.obj Y.obj f
  change (secondActionTranslation t).map ((firstCoordinateTranslation s).map
    (mkHom r.denom r.map.1 r.map.2)) =
    (firstCoordinateTranslation s).map ((secondActionTranslation t).map
      (mkHom r.denom r.map.1 r.map.2))
  rw [firstCoordinateTranslation_mkHom, secondActionTranslation_mkHom,
    secondActionTranslation_mkHom, firstCoordinateTranslation_mkHom]

end Braided

section Symmetric
variable [SymmetricCategory C]

/-- The common-denominator diagonal arrow naturally connects the identity
to the composite of opposite coordinate translations. -/
def actionDiagonalTranslation (s : C) :
    𝟭 (Localization C D) ⟶ firstCoordinateTranslation s ⋙ secondActionTranslation s where
  app X := mkHom s (β_ s X.obj.1).hom (𝟙 (s ⊙ₗ X.obj.2))
  naturality := by
    rintro X Y ⟨f⟩
    apply Quotient.sound
    refine ⟨β_ s f.denom, ?_⟩
    apply Prod.ext
    · change (β_ s f.denom).hom ▷ X.obj.1 ≫
        ((α_ f.denom s X.obj.1).hom ≫ f.denom ◁ (β_ s X.obj.1).hom ≫
          (𝟙 _ ≫ (α_ f.denom X.obj.1 s).inv ≫ f.map.1 ▷ s)) =
        (α_ s f.denom X.obj.1).hom ≫ s ◁ f.map.1 ≫ (β_ s Y.obj.1).hom
      rw [braiding_naturality_right]
      simp only [braiding_tensor_right_hom, Category.assoc, Iso.hom_inv_id_assoc,
        Category.id_comp]
    · change (β_ s f.denom).hom ⊵ₗ X.obj.2 ≫
        (αₗ f.denom s X.obj.2).hom ≫ f.denom ⊴ₗ 𝟙 (s ⊙ₗ X.obj.2) ≫
          MonoidalLeftAction.actionSwap s f.denom X.obj.2 ≫ s ⊴ₗ (𝟙 _ ≫ f.map.2) =
        (αₗ s f.denom X.obj.2).hom ≫ s ⊴ₗ f.map.2 ≫ 𝟙 _
      simp only [MonoidalLeftAction.actionSwap, MonoidalLeftAction.actionHomRight_id,
        Category.id_comp, Category.comp_id, Category.assoc, Iso.hom_inv_id_assoc,
        ← MonoidalLeftAction.comp_actionHomLeft_assoc, SymmetricCategory.symmetry,
        MonoidalLeftAction.id_actionHomLeft]

/-- The reverse composite has the same natural connection to the identity. -/
def actionDiagonalTranslationReverse (s : C) :
    𝟭 (Localization C D) ⟶ secondActionTranslation s ⋙ firstCoordinateTranslation s := by
  rw [← firstCoordinateTranslation_comp_secondAction]
  exact actionDiagonalTranslation s

end Symmetric
end CategoryTheory.GroupCompletion.Localization
