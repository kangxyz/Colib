/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.CategoryTheory.GroupCompletion.FirstCoordinateTranslation

/-!
Implementation provenance:
`Quillen/CategoryTheory/GroupCompletion/FirstCoordinateAssociativity.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Actual associativity and unit isomorphisms for first-coordinate translations -/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v'
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
namespace CategoryTheory.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]

/-- Translations vary functorially in their translating object. -/
def firstCoordinateBifunctor : C ⥤ (Localization C D ⥤ Localization C D) where
  obj := firstCoordinateTranslation
  map := firstCoordinateTranslationMap
  map_id s := by
    ext X
    change ActionLocalization.ofHom (C := C) (X := (X.obj.1 ⊗ s, X.obj.2))
      (Y := (X.obj.1 ⊗ s, X.obj.2)) (X.obj.1 ◁ 𝟙 s, 𝟙 X.obj.2) = 𝟙 _
    simpa only [whiskerLeft_id, CategoryTheory.prod_id] using
      ActionLocalization.ofHom_id (X.obj.1 ⊗ s, X.obj.2)
  map_comp {s t r} f g := by
    ext X
    change ActionLocalization.ofHom (C := C) (X := (X.obj.1 ⊗ s, X.obj.2))
      (Y := (X.obj.1 ⊗ r, X.obj.2)) (X.obj.1 ◁ (f ≫ g), 𝟙 X.obj.2) =
      ActionLocalization.ofHom (C := C) (X := (X.obj.1 ⊗ s, X.obj.2))
        (Y := (X.obj.1 ⊗ t, X.obj.2)) (X.obj.1 ◁ f, 𝟙 X.obj.2) ≫
      ActionLocalization.ofHom (C := C) (X := (X.obj.1 ⊗ t, X.obj.2))
        (Y := (X.obj.1 ⊗ r, X.obj.2)) (X.obj.1 ◁ g, 𝟙 X.obj.2)
    rw [← ActionLocalization.ofHom_comp]
    simp only [whiskerLeft_comp, Category.id_comp, CategoryTheory.prod_comp]

/-- The associator is an actual natural isomorphism of the quotient functors. -/
def firstCoordinateAssociator (s t : C) :
    firstCoordinateTranslation (D := D) (s ⊗ t) ≅
      firstCoordinateTranslation s ⋙ firstCoordinateTranslation t :=
  NatIso.ofComponents (fun X ↦ (ActionLocalization.ofFunctor (C := C) (D := C × D)).mapIso
    ((α_ X.obj.1 s t).symm.prod (Iso.refl X.obj.2))) (by
      intro X Y h
      obtain ⟨r, rfl⟩ := ActionLocalization.mkHom_surjective X.obj Y.obj h
      change (firstCoordinateTranslation (s ⊗ t)).map
        (mkHom r.denom r.map.1 r.map.2) ≫ ActionLocalization.ofHom _ =
        ActionLocalization.ofHom _ ≫ (firstCoordinateTranslation t).map
          ((firstCoordinateTranslation s).map (mkHom r.denom r.map.1 r.map.2))
      rw [firstCoordinateTranslation_mkHom, firstCoordinateTranslation_mkHom,
        firstCoordinateTranslation_mkHom]
      erw [ActionLocalization.mkHom_comp_ofHom, ActionLocalization.ofHom_comp_mkHom]
      apply congrArg ActionLocalization.mkHom
      apply congrArg (ActionLocalization.HomRep.mk r.denom)
      apply Prod.ext
      · change ((α_ r.denom X.obj.1 (s ⊗ t)).inv ≫ r.map.1 ▷ (s ⊗ t)) ≫
          (α_ Y.obj.1 s t).inv = r.denom ◁ (α_ X.obj.1 s t).inv ≫
          (α_ r.denom (X.obj.1 ⊗ s) t).inv ≫
          ((α_ r.denom X.obj.1 s).inv ≫ r.map.1 ▷ s) ▷ t
        rw [Category.assoc, associator_inv_naturality_left]
        simp only [comp_whiskerRight]
        simp only [pentagon_inv_assoc]
        rfl
      · change r.map.2 ≫ 𝟙 _ = r.denom ⊴ₗ 𝟙 _ ≫ r.map.2
        simp)

/-- Translation by the unit is naturally isomorphic to the identity. -/
def firstCoordinateUnitor : firstCoordinateTranslation (D := D) (𝟙_ C) ≅
    𝟭 (Localization C D) :=
  NatIso.ofComponents (fun X ↦ (ActionLocalization.ofFunctor (C := C) (D := C × D)).mapIso
    ((ρ_ X.obj.1).prod (Iso.refl X.obj.2))) (by
      intro X Y h
      obtain ⟨r, rfl⟩ := ActionLocalization.mkHom_surjective X.obj Y.obj h
      change (firstCoordinateTranslation (𝟙_ C)).map
        (mkHom r.denom r.map.1 r.map.2) ≫ ActionLocalization.ofHom _ =
        ActionLocalization.ofHom _ ≫ mkHom r.denom r.map.1 r.map.2
      rw [firstCoordinateTranslation_mkHom]
      erw [ActionLocalization.mkHom_comp_ofHom,
        ActionLocalization.ofHom_comp_mkHom]
      apply congrArg ActionLocalization.mkHom
      apply congrArg (ActionLocalization.HomRep.mk r.denom)
      apply Prod.ext
      · change ((α_ r.denom X.obj.1 (𝟙_ C)).inv ≫ r.map.1 ▷ (𝟙_ C)) ≫
          (ρ_ Y.obj.1).hom = r.denom ◁ (ρ_ X.obj.1).hom ≫ r.map.1
        rw [Category.assoc, rightUnitor_naturality]
        change (α_ r.denom X.obj.1 (𝟙_ C)).inv ≫
          (ρ_ (r.denom ⊗ X.obj.1)).hom ≫ r.map.1 = _
        simp only [rightUnitor_tensor_hom, Category.assoc, Iso.inv_hom_id_assoc]
      · change r.map.2 ≫ 𝟙 _ = r.denom ⊴ₗ 𝟙 _ ≫ r.map.2
        simp)

end CategoryTheory.GroupCompletion.Localization
