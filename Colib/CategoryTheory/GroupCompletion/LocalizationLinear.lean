/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.CategoryTheory.GroupCompletion.LocalizationFunctoriality

/-!
Implementation provenance:
`Quillen/CategoryTheory/GroupCompletion/LocalizationLinear.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Equivariance for the first-coordinate action after localization -/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u₁ v₁ u₂ v₂
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
namespace CategoryTheory.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type u₁} [Category.{v₁} D] [MonoidalLeftAction C D]
  {E : Type u₂} [Category.{v₂} E] [MonoidalLeftAction C E]
  (F : D ⥤ E) [F.LaxLeftLinear C]
attribute [local instance] firstCoordinateLeftAction

omit [BraidedCategory C] in
/-- First-coordinate translation strictly commutes with the original descended functor. -/
lemma map_firstCoordinateTranslation (s : C) {X Y : Localization C D} (f : X ⟶ Y) :
    (actedMapFunctor F).map ((firstCoordinateTranslation s).map f) =
      (firstCoordinateTranslation s).map ((actedMapFunctor F).map f) := by
  obtain ⟨r, rfl⟩ := ActionLocalization.mkHom_surjective X.obj Y.obj f
  change (actedMapFunctor F).map ((firstCoordinateTranslation s).map
    (mkHom r.denom r.map.1 r.map.2)) =
    (firstCoordinateTranslation s).map ((actedMapFunctor F).map (mkHom r.denom r.map.1 r.map.2))
  rw [firstCoordinateTranslation_mkHom]
  erw [actedMapFunctor_mkHom]
  rw [actedMapFunctor_mkHom]
  erw [firstCoordinateTranslation_mkHom]

/-- The induced functor preserves the complete first-coordinate action, with
identity lineators and the original associativity and unit maps. -/
instance actedMapFunctorFirstCoordinateLinear : (actedMapFunctor (C := C) F).LaxLeftLinear C where
  μₗ s X := 𝟙 _
  μₗ_naturality_left f X := by
    change secondFiberHom (F.obj X.obj.2) (X.obj.1 ◁ f) ≫ 𝟙 _ =
      𝟙 _ ≫ (actedMapFunctor F).map (secondFiberHom X.obj.2 (X.obj.1 ◁ f))
    rw [map_secondFiberHom, Category.id_comp, Category.comp_id]
  μₗ_naturality_right s _ _ f := by
    change (firstCoordinateTranslation s).map ((actedMapFunctor F).map f) ≫ 𝟙 _ =
      𝟙 _ ≫ (actedMapFunctor F).map ((firstCoordinateTranslation s).map f)
    rw [Category.id_comp, Category.comp_id, map_firstCoordinateTranslation]
  μₗ_associativity s t X := by
    change 𝟙 _ ≫ (actedMapFunctor F).map
      (secondFiberHom X.obj.2 (X.obj.1 ◁ (β_ t s).inv) ≫
        secondFiberHom X.obj.2 (α_ X.obj.1 t s).inv) =
      (secondFiberHom (F.obj X.obj.2) (X.obj.1 ◁ (β_ t s).inv) ≫
        secondFiberHom (F.obj X.obj.2) (α_ X.obj.1 t s).inv) ≫
          s ⊴ₗ 𝟙 (⟨(X.obj.1 ⊗ t, F.obj X.obj.2)⟩ : Localization C E) ≫ 𝟙 _
    rw [Functor.map_comp, map_secondFiberHom, map_secondFiberHom]
    simp only [Category.id_comp, Category.comp_id, MonoidalLeftAction.actionHomRight_id]
    exact (Category.comp_id _).symm
  μₗ_unitality X := by
    change (secondFiberHom (F.obj X.obj.2) (X.obj.1 ◁ 𝟙 (𝟙_ C)) ≫
      secondFiberHom (F.obj X.obj.2) (ρ_ X.obj.1).hom) =
      𝟙 _ ≫ (actedMapFunctor F).map (secondFiberHom X.obj.2 (X.obj.1 ◁ 𝟙 (𝟙_ C)) ≫
        secondFiberHom X.obj.2 (ρ_ X.obj.1).hom)
    rw [Functor.map_comp, map_secondFiberHom, map_secondFiberHom, Category.id_comp]

/-- The actual twice-localized functor. -/
def iteratedMap : Localization C (Localization C D) ⥤ Localization C (Localization C E) :=
  actedMapFunctor (actedMapFunctor F)

/-- Iteration commutes with the original canonical unit entries. -/
lemma iteratedMap_unitEntry :
    unitEntry (C := C) (D := Localization C D) ⋙ iteratedMap F =
      actedMapFunctor F ⋙ unitEntry := unitEntry_map (actedMapFunctor F)

/-- Twice-localized equivariance preserves the actual chosen fiber entry;
the common source functor on `C⁻¹C` is exactly the identity. -/
lemma iteratedFiberEntry_map (X : D) :
    iteratedFiberEntry X ⋙ iteratedMap (C := C) F = iteratedFiberEntry (F.obj X) := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro A B f
  change (iteratedMap F).map ((iteratedFiberEntry X).map f) =
    𝟙 _ ≫ (iteratedFiberEntry (F.obj X)).map f ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]
  obtain ⟨r, rfl⟩ := ActionLocalization.mkHom_surjective A.obj B.obj f
  change (iteratedMap F).map ((iteratedFiberEntry X).map
    (mkHom r.denom r.map.1 r.map.2)) =
    (iteratedFiberEntry (F.obj X)).map (mkHom r.denom r.map.1 r.map.2)
  rw [iteratedFiberEntry_mkHom, iteratedFiberEntry_mkHom]
  unfold iteratedMap
  erw [actedMapFunctor_mkHom]
  rw [map_secondFiberHom]
  change mkHom
    (X := (A.obj.1, (⟨(A.obj.2, F.obj X)⟩ : Localization C E)))
    (Y := (B.obj.1, (⟨(B.obj.2, F.obj X)⟩ : Localization C E))) r.denom r.map.1 (𝟙 _ ≫
    secondFiberHom (F.obj X) ((β_ A.obj.2 r.denom).hom ≫ r.map.2)) = _
  rw [Category.id_comp]

end CategoryTheory.GroupCompletion.Localization
