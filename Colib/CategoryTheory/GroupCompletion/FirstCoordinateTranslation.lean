/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.SecondProjection

/-!
Implementation provenance:
`Quillen/CategoryTheory/GroupCompletion/FirstCoordinateTranslation.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # First-coordinate translations over the action category

These functors preserve the actual second-coordinate projection. They are the
first-coordinate translations for arbitrary acted-on categories; no action of
the actor on the acted-on category's tensor product is required.
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v'
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
namespace CategoryTheory.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]

/-- Right tensor the first coordinate and retain the acted-on object. -/
def firstCoordinateTensor (s : C) : C × D ⥤ C × D :=
  (tensorRight s).prod (𝟭 D)

instance firstCoordinateTensorLinear (s : C) :
    (firstCoordinateTensor (D := D) s).LaxLeftLinear C where
  μₗ t X := ((α_ t X.1 s).inv, 𝟙 _)
  μₗ_naturality_left f X := by
    apply Prod.ext
    · exact associator_inv_naturality_left f X.1 s
    · change (f ⊵ₗ X.2) ≫ 𝟙 _ = 𝟙 _ ≫ (f ⊵ₗ X.2)
      simp
  μₗ_naturality_right t _ _ f := by
    apply Prod.ext
    · exact associator_inv_naturality_middle t f.1 s
    · change (t ⊴ₗ f.2) ≫ 𝟙 _ = 𝟙 _ ≫ (t ⊴ₗ f.2)
      simp
  μₗ_associativity t r X := by
    apply Prod.ext
    · exact pentagon_hom_inv_inv_inv_hom.symm
    · change 𝟙 _ ≫ (αₗ t r X.2).hom =
        (αₗ t r X.2).hom ≫ t ⊴ₗ 𝟙 _ ≫ 𝟙 _
      simp
  μₗ_unitality X := by
    apply Prod.ext
    · exact leftUnitor_tensor_hom X.1 s
    · change (λₗ[C] X.2).hom = 𝟙 _ ≫ (λₗ[C] X.2).hom
      simp

/-- The actual quotient functor translating just the first coordinate. -/
def firstCoordinateTranslation (s : C) : Localization C D ⥤ Localization C D :=
  ActionLocalization.mapFunctor (firstCoordinateTensor s)

@[simp]
theorem firstCoordinateTranslation_obj (s : C) (X : Localization C D) :
    (firstCoordinateTranslation s).obj X = ⟨(X.obj.1 ⊗ s, X.obj.2)⟩ := rfl

@[simp]
theorem firstCoordinateTranslation_mkHom (s : C) {X Y : C × D}
    (t : C) (f : t ⊗ X.1 ⟶ Y.1) (g : t ⊙ₗ X.2 ⟶ Y.2) :
    (firstCoordinateTranslation s).map (mkHom t f g) =
      mkHom (X := (X.1 ⊗ s, X.2)) (Y := (Y.1 ⊗ s, Y.2))
        t ((α_ t X.1 s).inv ≫ f ▷ s) g := by
  change ActionLocalization.mkHom (X := (X.1 ⊗ s, X.2))
    (Y := (Y.1 ⊗ s, Y.2)) ⟨t, (_, 𝟙 _ ≫ g)⟩ = _
  simp only [Category.id_comp]
  rfl

/-- The first-coordinate translation is over the unchanged action category. -/
theorem firstCoordinateTranslation_comp_secondProjection (s : C) :
    firstCoordinateTranslation (D := D) s ⋙ secondProjection = secondProjection := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro X Y f
  obtain ⟨r, rfl⟩ := ActionLocalization.mkHom_surjective X.obj Y.obj f
  change secondProjection.map ((firstCoordinateTranslation s).map
    (mkHom r.denom r.map.1 r.map.2)) = 𝟙 _ ≫
      secondProjection.map (mkHom r.denom r.map.1 r.map.2) ≫ 𝟙 _
  simp only [firstCoordinateTranslation_mkHom, secondProjection_mkHom,
    Category.id_comp, Category.comp_id]

/-- Morphisms of translating objects act in the first coordinate. -/
def firstCoordinateTensorMap {s t : C} (f : s ⟶ t) :
    firstCoordinateTensor (D := D) s ⟶ firstCoordinateTensor t where
  app X := (X.1 ◁ f, 𝟙 X.2)
  naturality {X Y} g := by
    apply Prod.ext
    · exact (whisker_exchange g.1 f).symm
    · change g.2 ≫ 𝟙 Y.2 = 𝟙 X.2 ≫ g.2
      simp

/-- Naturality in the translating object descends through denominator isomorphisms. -/
def firstCoordinateTranslationMap {s t : C} (f : s ⟶ t) :
    firstCoordinateTranslation (D := D) s ⟶ firstCoordinateTranslation t :=
  ActionLocalization.mapNatTrans (firstCoordinateTensor s) (firstCoordinateTensorMap f)
    (fun r X ↦ by
      apply Prod.ext
      · exact (associator_inv_naturality_right r X.1 f).symm
      · change 𝟙 _ ≫ 𝟙 _ = r ⊴ₗ 𝟙 X.2 ≫ 𝟙 _
        simp)

@[simp]
theorem firstCoordinateTranslationMap_app {s t : C} (f : s ⟶ t)
    (X : Localization C D) :
    (firstCoordinateTranslationMap f).app X =
      ActionLocalization.ofHom (C := C) (X := (X.obj.1 ⊗ s, X.obj.2))
        (Y := (X.obj.1 ⊗ t, X.obj.2)) (X.obj.1 ◁ f, 𝟙 X.obj.2) := rfl

end CategoryTheory.GroupCompletion.Localization
