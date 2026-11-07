/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.CategoryTheory.GroupCompletion.FirstCoordinateAction
public import Colib.CategoryTheory.GroupCompletion.TrivialAction

/-!
Implementation provenance:
`Quillen/CategoryTheory/GroupCompletion/SecondProjectionLinear.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # The second projection is linear for first-coordinate translation -/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v'
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
namespace CategoryTheory.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]

@[simp]
theorem secondProjection_secondFiberHom (X : D) {A B : C} (f : A ⟶ B) :
    secondProjection.map (secondFiberHom X f) = 𝟙 (⟨X⟩ : ActionLocalization C D) := by
  rw [secondFiberHom, secondProjection_ofHom, ActionLocalization.ofHom_id]

@[simp]
theorem secondProjection_firstCoordinateTranslation (s : C)
    {X Y : Localization C D} (f : X ⟶ Y) :
    secondProjection.map ((firstCoordinateTranslation s).map f) =
      secondProjection.map f :=
  by
    obtain ⟨r, rfl⟩ := ActionLocalization.mkHom_surjective X.obj Y.obj f
    change secondProjection.map ((firstCoordinateTranslation s).map
      (mkHom r.denom r.map.1 r.map.2)) = _
    rw [firstCoordinateTranslation_mkHom]
    rfl

variable [BraidedCategory C]
attribute [local instance] firstCoordinateLeftAction

theorem secondProjection_firstCoordinateUnitor (X : Localization C D) :
    secondProjection.map (λₗ[C] X).hom = 𝟙 (secondProjection.obj X) := by
  change secondProjection.map (secondFiberHom X.obj.2 (X.obj.1 ◁ 𝟙 (𝟙_ C)) ≫
    secondFiberHom X.obj.2 (ρ_ X.obj.1).hom) = _
  simp only [whiskerLeft_id, secondFiberHom_id, Category.id_comp]
  exact secondProjection_secondFiberHom X.obj.2 (ρ_ X.obj.1).hom

theorem secondProjection_firstCoordinateAssociator (s t : C) (X : Localization C D) :
    secondProjection.map (αₗ s t X).hom = 𝟙 (secondProjection.obj X) := by
  change secondProjection.map
    (secondFiberHom X.obj.2 (X.obj.1 ◁ (β_ t s).inv) ≫
      secondFiberHom X.obj.2 (α_ X.obj.1 t s).inv) = _
  simp only [Functor.map_comp, secondProjection_secondFiberHom]
  exact Category.id_comp _

/-- The second projection target carries the trivial actor action. -/
local instance trivialSecondProjectionTarget : MonoidalLeftAction C (ActionLocalization C D) :=
  MonoidalLeftAction.trivial C (ActionLocalization C D)

/-- The second projection is linear when its target has the named trivial
actor action. Every component of the lineator is the actual identity. -/
instance secondProjectionFirstCoordinateLinear :
    (secondProjection (C := C) (D := D)).LaxLeftLinear C where
  μₗ s X := 𝟙 _
  μₗ_naturality_left f X := by
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ secondProjection.map (f ⊵ₗ X)
    rw [firstCoordinateLeftAction_actorMap, secondProjection_secondFiberHom]
    rfl
  μₗ_naturality_right s _ _ f := by
    change secondProjection.map f ≫ 𝟙 _ =
      𝟙 _ ≫ secondProjection.map (s ⊴ₗ f)
    rw [firstCoordinateLeftAction_map, secondProjection_firstCoordinateTranslation]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  μₗ_associativity s t X := by
    change 𝟙 _ ≫ secondProjection.map (αₗ s t X).hom = 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
    rw [secondProjection_firstCoordinateAssociator]
    simp only [Category.id_comp]
    rfl
  μₗ_unitality X := by
    change 𝟙 _ = 𝟙 _ ≫ secondProjection.map (λₗ[C] X).hom
    rw [secondProjection_firstCoordinateUnitor, Category.id_comp]
    rfl

/-- The actual iterated projection used in Grayson's comparison diagram.
The source is a second independent action localization of the same `C⁻¹D`.
No fiber identification or homotopy-equivalence condition is assumed here. -/
def iteratedSecondProjection :
    Localization C (Localization C D) ⥤ ActionLocalization C D :=
  secondProjection ⋙ ActionLocalization.mapFunctor
    (secondProjection (C := C) (D := D)) ⋙
      ActionLocalization.TrivialAction.forgetFunctor C (ActionLocalization C D)

@[simp]
theorem iteratedSecondProjection_obj (X : Localization C (Localization C D)) :
    iteratedSecondProjection.obj X = ⟨X.obj.2.obj.2⟩ := rfl

@[simp]
theorem iteratedSecondProjection_mkHom {X Y : C × Localization C D}
    (s : C) (f : s ⊗ X.1 ⟶ Y.1) (g : s ⊙ₗ X.2 ⟶ Y.2) :
    iteratedSecondProjection.map (mkHom s f g) = secondProjection.map g := by
  dsimp only [iteratedSecondProjection, Functor.comp_map]
  rw [secondProjection_mkHom, ActionLocalization.mapFunctor_mkHom,
    ActionLocalization.TrivialAction.forgetFunctor_map_mkHom]
  change 𝟙 _ ≫ secondProjection.map g = secondProjection.map g
  exact Category.id_comp _

end CategoryTheory.GroupCompletion.Localization
