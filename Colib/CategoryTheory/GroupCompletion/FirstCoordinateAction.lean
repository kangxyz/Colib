/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.CategoryTheory.GroupCompletion.FirstCoordinateAssociativity
public import Colib.CategoryTheory.GroupCompletion.SecondProjectionCocartesian
public import Mathlib.CategoryTheory.Monoidal.Action.End
public import Mathlib.CategoryTheory.Monoidal.Action.Opposites
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
Implementation provenance:
`Quillen/CategoryTheory/GroupCompletion/FirstCoordinateAction.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # The first-coordinate monoidal action on Grayson's localization -/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v'
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
namespace CategoryTheory.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]
attribute [local instance] endofunctorMonoidalCategory

@[simp]
theorem firstCoordinateTranslation_secondFiberHom (s : C) (X : D)
    {A B : C} (f : A ⟶ B) :
    (firstCoordinateTranslation s).map (secondFiberHom X f) =
      secondFiberHom X (f ▷ s) :=
  ActionLocalization.mapFunctor_ofHom (firstCoordinateTensor s)
    (X := (A, X)) (Y := (B, X)) (f, 𝟙 X)

@[simp]
theorem secondFiberHom_comp (X : D) {A B T : C} (f : A ⟶ B) (g : B ⟶ T) :
    secondFiberHom X f ≫ secondFiberHom X g = secondFiberHom X (f ≫ g) := by
  dsimp only [secondFiberHom]
  rw [← ActionLocalization.ofHom_comp]
  simp only [CategoryTheory.prod_comp, Category.id_comp]

@[simp]
theorem secondFiberHom_id (X : D) (A : C) :
    secondFiberHom X (𝟙 A) = 𝟙 _ := ActionLocalization.ofHom_id (A, X)


instance firstCoordinateBifunctorMonoidal :
    (firstCoordinateBifunctor (C := C) (D := D)).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := firstCoordinateUnitor.symm
      μIso := fun s t ↦ (firstCoordinateAssociator s t).symm
      μIso_hom_natural_left := by
        intro s t f r
        ext X
        change (firstCoordinateTranslation r).map
          (secondFiberHom X.obj.2 (X.obj.1 ◁ f)) ≫
            secondFiberHom X.obj.2 ((α_ X.obj.1 t r).hom) =
          secondFiberHom X.obj.2 ((α_ X.obj.1 s r).hom) ≫
            secondFiberHom X.obj.2 (X.obj.1 ◁ (f ▷ r))
        rw [firstCoordinateTranslation_secondFiberHom, secondFiberHom_comp,
          secondFiberHom_comp]
        apply congrArg (secondFiberHom X.obj.2)
        exact associator_naturality_middle X.obj.1 f r
      μIso_hom_natural_right := by
        intro s t r f
        ext X
        change secondFiberHom X.obj.2 ((X.obj.1 ⊗ r) ◁ f) ≫
            secondFiberHom X.obj.2 ((α_ X.obj.1 r t).hom) =
          secondFiberHom X.obj.2 ((α_ X.obj.1 r s).hom) ≫
            secondFiberHom X.obj.2 (X.obj.1 ◁ (r ◁ f))
        rw [secondFiberHom_comp, secondFiberHom_comp]
        apply congrArg (secondFiberHom X.obj.2)
        exact associator_naturality_right X.obj.1 r f
      associativity := by
        intro s t r
        ext X
        change (firstCoordinateTranslation r).map
          (secondFiberHom X.obj.2 ((α_ X.obj.1 s t).hom)) ≫
            secondFiberHom X.obj.2 ((α_ X.obj.1 (s ⊗ t) r).hom) ≫
              secondFiberHom X.obj.2 (X.obj.1 ◁ (α_ s t r).hom) =
          𝟙 _ ≫ secondFiberHom X.obj.2 ((α_ (X.obj.1 ⊗ s) t r).hom) ≫
            secondFiberHom X.obj.2 ((α_ X.obj.1 s (t ⊗ r)).hom)
        rw [firstCoordinateTranslation_secondFiberHom]
        simp only [Category.id_comp, secondFiberHom_comp]
        apply congrArg (secondFiberHom X.obj.2)
        exact pentagon X.obj.1 s t r
      left_unitality := by
        intro s
        ext X
        change 𝟙 _ = (firstCoordinateTranslation s).map
          (secondFiberHom X.obj.2 ((ρ_ X.obj.1).inv)) ≫
            secondFiberHom X.obj.2 ((α_ X.obj.1 (𝟙_ C) s).hom) ≫
              secondFiberHom X.obj.2 (X.obj.1 ◁ (λ_ s).hom)
        rw [firstCoordinateTranslation_secondFiberHom]
        simp only [secondFiberHom_comp]
        erw [← secondFiberHom_id X.obj.2 (X.obj.1 ⊗ s)]
        apply congrArg (secondFiberHom X.obj.2)
        change 𝟙 _ = (ρ_ X.obj.1).inv ▷ s ≫
            (α_ X.obj.1 (𝟙_ C) s).hom ≫ X.obj.1 ◁ (λ_ s).hom
        monoidal
      right_unitality := by
        intro s
        ext X
        change 𝟙 _ = secondFiberHom X.obj.2 ((ρ_ (X.obj.1 ⊗ s)).inv) ≫
          secondFiberHom X.obj.2 ((α_ X.obj.1 s (𝟙_ C)).hom) ≫
            secondFiberHom X.obj.2 (X.obj.1 ◁ (ρ_ s).hom)
        simp only [secondFiberHom_comp]
        erw [← secondFiberHom_id X.obj.2 (X.obj.1 ⊗ s)]
        apply congrArg (secondFiberHom X.obj.2)
        monoidal
        }

/-- Right tensor on the first coordinate, with all coherence inherited from
its actual strong monoidal functor to endofunctors. -/
@[instance_reducible]
def firstCoordinateRightAction : MonoidalRightAction C (Localization C D) :=
  MonoidalRightAction.actionOfMonoidalFunctorToEndofunctor firstCoordinateBifunctor

/-- In the braided case the same first-coordinate translations define a left
action. The braiding needed to reverse composition is supplied by mathlib's
strong monoidal functor to the monoidal opposite, with no strictification. -/
@[instance_reducible]
def firstCoordinateLeftAction [BraidedCategory C] :
    MonoidalLeftAction C (Localization C D) := by
  letI := firstCoordinateRightAction (C := C) (D := D)
  letI := MonoidalLeftAction.monoidalOppositeLeftAction C (Localization C D)
  exact MonoidalLeftAction.actionOfMonoidalFunctorToEndofunctorMop
    (mopFunctor C ⋙
      MonoidalLeftAction.curriedActionMop Cᴹᵒᵖ (Localization C D))

section Braided
variable [BraidedCategory C]
attribute [local instance] firstCoordinateLeftAction

theorem firstCoordinateLeftAction_obj (s : C) (X : Localization C D) :
    s ⊙ₗ X = ⟨(X.obj.1 ⊗ s, X.obj.2)⟩ := rfl

theorem firstCoordinateLeftAction_map (s : C) {X Y : Localization C D}
    (f : X ⟶ Y) : s ⊴ₗ f = (firstCoordinateTranslation s).map f := rfl

theorem firstCoordinateLeftAction_actorMap {s t : C} (f : s ⟶ t)
    (X : Localization C D) :
    f ⊵ₗ X = secondFiberHom X.obj.2 (X.obj.1 ◁ f) := rfl

end Braided
end CategoryTheory.GroupCompletion.Localization
