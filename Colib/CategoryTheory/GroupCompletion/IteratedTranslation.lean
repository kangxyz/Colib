/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.CategoryTheory.GroupCompletion.IteratedCocartesian
public import Colib.CategoryTheory.GroupCompletion.Translation

/-!
Implementation provenance:
`Quillen/CategoryTheory/GroupCompletion/IteratedTranslation.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Actual translation squares for the iterated projection -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v'
open CategoryTheory MonoidalCategory BraidedCategory
open scoped MonoidalLeftAction
namespace CategoryTheory.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]
attribute [local instance] firstCoordinateLeftAction

private theorem translation_braiding {B B' : C} (s u : C) (h : u ⊗ B ⟶ B') :
    s ◁ ((β_ B u).hom ≫ h) ≫ (β_ s B').hom =
      (α_ s B u).inv ≫ (β_ s B).hom ▷ u ≫ (β_ (B ⊗ s) u).hom ≫
        (α_ u B s).inv ≫ h ▷ s := by
  simp only [whiskerLeft_comp, Category.assoc]
  rw [braiding_naturality_right, braiding_naturality_right_assoc]
  simp only [braiding_tensor_right_hom, braiding_tensor_left_hom, Category.assoc,
    Iso.hom_inv_id_assoc]

/-- A canonical inner lift with its target expressed as right translation. -/
def secondRightLift {X Y : D} (s : C) (g : s ⊙ₗ X ⟶ Y) (B : C) :
    (⟨(B, X)⟩ : Localization C D) ⟶ ⟨(B ⊗ s, Y)⟩ :=
  mkHom s (β_ s B).hom g

/-- The corresponding lift in the iterated category fixes the outer actor. -/
def iteratedRightLift {X Y : D} (s : C) (g : s ⊙ₗ X ⟶ Y) (A B : C) :
    (⟨(A, ⟨(B, X)⟩)⟩ : Localization C (Localization C D)) ⟶
      ⟨(A, ⟨(B ⊗ s, Y)⟩)⟩ :=
  ActionLocalization.ofHom (C := C)
    (X := (A, (⟨(B, X)⟩ : Localization C D)))
    (Y := (A, (⟨(B ⊗ s, Y)⟩ : Localization C D))) (𝟙 A, secondRightLift s g B)

@[simp]
theorem iteratedSecondProjection_iteratedRightLift {X Y : D} (s : C)
    (g : s ⊙ₗ X ⟶ Y) (A B : C) :
    iteratedSecondProjection.map (iteratedRightLift s g A B) =
      ActionLocalization.mkHom ⟨s, g⟩ := by
  rw [iteratedRightLift, iteratedSecondProjection_ofHom, secondRightLift,
    secondProjection_mkHom]

omit [BraidedCategory C] in
/-- The existing second-coordinate translation acts on representatives by
its original associator. -/
theorem secondTranslation_mkHom (s : C) {A B : C × C} (u : C)
    (f : u ⊗ A.1 ⟶ B.1) (g : u ⊗ A.2 ⟶ B.2) :
    (secondTranslation s).map (mkHom u f g) =
      mkHom (X := (A.1, A.2 ⊗ s)) (Y := (B.1, B.2 ⊗ s)) u f
        ((α_ u A.2 s).inv ≫ g ▷ s) := by
  change ActionLocalization.mkHom (X := (A.1, A.2 ⊗ s)) (Y := (B.1, B.2 ⊗ s))
    ⟨u, (𝟙 _ ≫ f, _)⟩ = _
  rw [Category.id_comp]
  rfl

/-- The chosen lifts intertwine exactly the existing `secondTranslation`,
not an abstractly equivalent replacement for it. -/
theorem iteratedRightLift_naturality {X Y : D} (s : C) (g : s ⊙ₗ X ⟶ Y)
    {A B : Localization C C} (f : A ⟶ B) :
    (iteratedFiberEntry X).map f ≫ iteratedRightLift s g B.obj.1 B.obj.2 =
      iteratedRightLift s g A.obj.1 A.obj.2 ≫
        (iteratedFiberEntry Y).map ((secondTranslation s).map f) := by
  obtain ⟨r, rfl⟩ := ActionLocalization.mkHom_surjective A.obj B.obj f
  change (iteratedFiberEntry X).map (mkHom r.denom r.map.1 r.map.2) ≫ _ =
    _ ≫ (iteratedFiberEntry Y).map ((secondTranslation s).map
      (mkHom r.denom r.map.1 r.map.2))
  rw [iteratedFiberEntry_mkHom, secondTranslation_mkHom, iteratedFiberEntry_mkHom]
  dsimp only [iteratedRightLift, mkHom]
  erw [ActionLocalization.mkHom_comp_ofHom, ActionLocalization.ofHom_comp_mkHom]
  apply congrArg ActionLocalization.mkHom
  apply congrArg (ActionLocalization.HomRep.mk r.denom)
  apply Prod.ext
  · change r.map.1 ≫ 𝟙 _ = r.denom ◁ 𝟙 _ ≫ r.map.1
    simp
  · change secondFiberHom X ((β_ A.obj.2 r.denom).hom ≫ r.map.2) ≫
        secondRightLift s g B.obj.2 =
      r.denom ⊴ₗ secondRightLift s g A.obj.2 ≫
        secondFiberHom Y ((β_ (A.obj.2 ⊗ s) r.denom).hom ≫
          (α_ r.denom A.obj.2 s).inv ≫ r.map.2 ▷ s)
    rw [firstCoordinateLeftAction_map]
    dsimp only [secondRightLift]
    rw [firstCoordinateTranslation_mkHom]
    dsimp only [secondFiberHom, mkHom]
    erw [ActionLocalization.ofHom_comp_mkHom, ActionLocalization.mkHom_comp_ofHom]
    apply congrArg ActionLocalization.mkHom
    apply congrArg (ActionLocalization.HomRep.mk s)
    apply Prod.ext
    · change s ◁ ((β_ A.obj.2 r.denom).hom ≫ r.map.2) ≫ (β_ s B.obj.2).hom =
        ((α_ s A.obj.2 r.denom).inv ≫ (β_ s A.obj.2).hom ▷ r.denom) ≫
          (β_ (A.obj.2 ⊗ s) r.denom).hom ≫ (α_ r.denom A.obj.2 s).inv ≫ r.map.2 ▷ s
      simpa only [Category.assoc] using translation_braiding s r.denom r.map.2
    · change s ⊴ₗ 𝟙 X ≫ g = g ≫ 𝟙 Y
      simp

/-- The fiber isomorphism used to express a lift by right translation. -/
def iteratedLiftTargetIso (Y : D) (s A B : C) :
    (⟨(A, ⟨(s ⊗ B, Y)⟩)⟩ : Localization C (Localization C D)) ≅
      ⟨(A, ⟨(B ⊗ s, Y)⟩)⟩ :=
  (ActionLocalization.ofFunctor (C := C) (D := C × Localization C D)).mapIso
    ((Iso.refl A).prod ((fixedSecondEntry Y).mapIso (β_ s B)))

/-- This change of target is an actual isomorphism after the canonical lift. -/
theorem iteratedRightLift_eq {X Y : D} (s : C) (g : s ⊙ₗ X ⟶ Y) (A B : C) :
    iteratedRightLift s g A B =
      iteratedLift s g A B ≫ (iteratedLiftTargetIso Y s A B).hom := by
  change ActionLocalization.ofHom (C := C)
    (X := (A, (⟨(B, X)⟩ : Localization C D)))
    (Y := (A, (⟨(B ⊗ s, Y)⟩ : Localization C D))) (𝟙 A, secondRightLift s g B) =
      ActionLocalization.ofHom (C := C)
        (X := (A, (⟨(B, X)⟩ : Localization C D)))
        (Y := (A, (⟨(s ⊗ B, Y)⟩ : Localization C D))) (𝟙 A, secondLift s g B) ≫
      ActionLocalization.ofHom (C := C)
        (X := (A, (⟨(s ⊗ B, Y)⟩ : Localization C D)))
        (Y := (A, (⟨(B ⊗ s, Y)⟩ : Localization C D)))
        (𝟙 A, secondFiberHom Y (β_ s B).hom)
  rw [← ActionLocalization.ofHom_comp]
  apply congrArg ActionLocalization.ofHom
  apply Prod.ext
  · exact (Category.id_comp _).symm
  · change secondRightLift s g B = secondLift s g B ≫ secondFiberHom Y (β_ s B).hom
    dsimp only [secondRightLift, secondLift, secondFiberHom, mkHom]
    rw [ActionLocalization.mkHom_comp_ofHom]
    apply congrArg ActionLocalization.mkHom
    apply congrArg (ActionLocalization.HomRep.mk s)
    change ((β_ s B).hom, g) = (𝟙 _ ≫ (β_ s B).hom, g ≫ 𝟙 Y)
    simp

section Cocartesian
variable [∀ X : D, (MonoidalLeftAction.actionRight C X).Faithful]
  [∀ (X Y : D) (f : X ⟶ Y), Mono f]

instance iteratedRightLift_stronglyCocartesian {X Y : D} (s : C)
    (g : s ⊙ₗ X ⟶ Y) (A B : C) :
    iteratedSecondProjection.IsStronglyCocartesian
      (iteratedSecondProjection.map (iteratedRightLift s g A B))
      (iteratedRightLift s g A B) := by
  rw [iteratedRightLift_eq, Functor.map_comp]
  infer_instance

end Cocartesian

/-- The transport square is represented by an actual natural transformation
whose components are the explicit lifts. -/
def iteratedTranslationLift {X Y : D} (s : C) (g : s ⊙ₗ X ⟶ Y) :
    iteratedFiberEntry X ⟶ secondTranslation s ⋙ iteratedFiberEntry Y where
  app A := iteratedRightLift s g A.obj.1 A.obj.2
  naturality {_ _} f := iteratedRightLift_naturality s g f

@[simp]
theorem iteratedTranslationLift_app {X Y : D} (s : C) (g : s ⊙ₗ X ⟶ Y)
    (A : Localization C C) :
    (iteratedTranslationLift s g).app A = iteratedRightLift s g A.obj.1 A.obj.2 := rfl

end CategoryTheory.GroupCompletion.Localization
