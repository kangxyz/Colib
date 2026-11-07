/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.SecondProjectionFiber
public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian

/-!
Implementation provenance:
`Quillen/CategoryTheory/GroupCompletion/SecondProjectionCocartesian.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Cocartesian lifts and actual fiber translations for the second projection -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v'
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
namespace CategoryTheory.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]

/-- These are the actual morphisms of the identified strict fibers. -/
def secondFiberHom (X : D) {A B : C} (f : A ⟶ B) :
    (⟨(A, X)⟩ : Localization C D) ⟶ ⟨(B, X)⟩ :=
  ActionLocalization.ofHom (C := C) (X := (A, X)) (Y := (B, X)) (f, 𝟙 X)

/-- The cocartesian transport along a representative `(s,g)` is exactly left
tensoring by `s` on the original actor category identified with each fiber. -/
theorem secondLift_naturality {X Y : D} (s : C) (g : s ⊙ₗ X ⟶ Y)
    {A B : C} (f : A ⟶ B) :
    secondFiberHom X f ≫ secondLift s g B =
      secondLift s g A ≫ secondFiberHom Y (s ◁ f) := by
  dsimp only [secondFiberHom, secondLift, mkHom]
  rw [ActionLocalization.ofHom_comp_mkHom, ActionLocalization.mkHom_comp_ofHom]
  apply congrArg ActionLocalization.mkHom
  apply congrArg (ActionLocalization.HomRep.mk s)
  change (s ◁ f ≫ 𝟙 _, s ⊴ₗ 𝟙 X ≫ g) = (𝟙 _ ≫ s ◁ f, g ≫ 𝟙 Y)
  simp

variable [∀ X : D, (MonoidalLeftAction.actionRight C X).Faithful]
  [∀ (X Y : D) (f : X ⟶ Y), Mono f]

/-- The representative lifts satisfy the standard strong cocartesian predicate. -/
instance secondLift_stronglyCocartesian {X Y : D} (s : C)
    (g : s ⊙ₗ X ⟶ Y) (A : C) :
    secondProjection.IsStronglyCocartesian
      (secondProjection.map (secondLift s g A)) (secondLift s g A) where
  universal_property' {Z} w h _ := by
    have hh := (IsHomLift.eq_of_isHomLift secondProjection
      (secondProjection.map (secondLift s g A) ≫ w) h).symm
    rw [secondProjection_secondLift] at hh
    obtain ⟨l, hl, hu⟩ := secondLift_universal s g A Z.obj.1 w h hh
    refine ⟨l, ⟨?_, hl.2⟩, ?_⟩
    · rw [← hl.1]
      exact IsHomLift.map secondProjection l
    · intro l' hl'
      let := hl'.1
      exact hu l' ⟨(IsHomLift.eq_of_isHomLift secondProjection w l').symm, hl'.2⟩

/-- Every base arrow has an actual strong cocartesian lift, with strict target
projection equality. No homotopy-equivalence hypothesis is used. -/
theorem exists_secondProjectionLift (A : Localization C D) (Y : ActionLocalization C D)
    (g : secondProjection.obj A ⟶ Y) :
    ∃ (B : Localization C D) (f : A ⟶ B),
      secondProjection.obj B = Y ∧
        secondProjection.IsStronglyCocartesian g f := by
  obtain ⟨r, rfl⟩ := ActionLocalization.mkHom_surjective A.obj.2 Y.obj g
  refine ⟨⟨(r.denom ⊗ A.obj.1, Y.obj)⟩, secondLift r.denom r.map A.obj.1, rfl, ?_⟩
  rw [← secondProjection_secondLift r.denom r.map A.obj.1]
  infer_instance

end CategoryTheory.GroupCompletion.Localization
