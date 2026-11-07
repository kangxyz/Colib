/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.CategoryTheory.Monoidal.Action.LinearFunctor
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
Implementation provenance:
`Quillen/Aglib/CategoryTheory/Monoidal/Action/Braided.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Braided actor translations are linear functors -/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v'
open CategoryTheory MonoidalCategory BraidedCategory
open scoped MonoidalLeftAction
namespace CategoryTheory.MonoidalCategory.MonoidalLeftAction
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]

/-- The actor associator acts by the actual action pentagon, solved for the
single actor morphism. This normal form retains every structure isomorphism. -/
lemma associatorHom_actionHomLeft (s t r : C) (X : D) :
    (α_ s t r).hom ⊵ₗ X =
      (αₗ (s ⊗ t) r X).hom ≫ (αₗ s t (r ⊙ₗ X)).hom ≫
        s ⊴ₗ (αₗ t r X).inv ≫ (αₗ s (t ⊗ r) X).inv := by
  apply (cancel_mono (αₗ s (t ⊗ r) X).hom).1
  apply (cancel_mono (s ⊴ₗ (αₗ t r X).hom)).1
  simp only [Category.assoc, Iso.inv_hom_id_assoc, actionHomRight_inv_hom,
    Category.comp_id]
  exact associator_actionHom s t r X

/-- Inverse actor associators satisfy the inverse action pentagon. -/
lemma associatorInv_actionHomLeft (s t r : C) (X : D) :
    (α_ s t r).inv ⊵ₗ X =
      (αₗ s (t ⊗ r) X).hom ≫ s ⊴ₗ (αₗ t r X).hom ≫
        (αₗ s t (r ⊙ₗ X)).inv ≫ (αₗ (s ⊗ t) r X).inv := by
  apply (cancel_epi ((α_ s t r).hom ⊵ₗ X)).1
  rw [hom_inv_actionHomLeft, associatorHom_actionHomLeft]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, actionHomRight_inv_hom_assoc,
    Iso.hom_inv_id_assoc, Iso.hom_inv_id]

variable [BraidedCategory C]

/-- The actual interchange between two successive actor translations. -/
def actionSwap (s t : C) (X : D) : t ⊙ₗ s ⊙ₗ X ⟶ s ⊙ₗ t ⊙ₗ X :=
  (αₗ t s X).inv ≫ (β_ t s).hom ⊵ₗ X ≫ (αₗ s t X).hom

/-- The action interchange obeys the linear associativity law. -/
lemma actionSwap_associativity (s t r : C) (X : D) :
    actionSwap s (t ⊗ r) X ≫ s ⊴ₗ (αₗ t r X).hom =
      (αₗ t r (s ⊙ₗ X)).hom ≫ t ⊴ₗ actionSwap s r X ≫
        actionSwap s t (r ⊙ₗ X) := by
  dsimp only [actionSwap]
  rw [braiding_tensor_left_hom]
  simp only [comp_actionHomLeft, associatorHom_actionHomLeft,
    associatorInv_actionHomLeft, whiskerLeft_actionHomLeft, whiskerRight_actionHomLeft,
    actionHomRight_comp, Category.assoc, Iso.inv_hom_id_assoc,
    actionHomRight_inv_hom, Category.comp_id]

/-- Naturality of the interchange in the translating actor. -/
lemma actionSwap_naturality_actor (s : C) {t r : C} (f : t ⟶ r) (X : D) :
    f ⊵ₗ (s ⊙ₗ X) ≫ actionSwap s r X =
      actionSwap s t X ≫ s ⊴ₗ (f ⊵ₗ X) := by
  have h₁ : f ⊵ₗ (s ⊙ₗ X) ≫ (αₗ r s X).inv =
      (αₗ t s X).inv ≫ (f ▷ s) ⊵ₗ X := by
    simp
  have h₂ : (s ◁ f) ⊵ₗ X ≫ (αₗ s r X).hom =
      (αₗ s t X).hom ≫ s ⊴ₗ (f ⊵ₗ X) := by
    simp
  simp only [actionSwap, Category.assoc]
  rw [reassoc_of% h₁, ← comp_actionHomLeft_assoc, braiding_naturality_left,
    comp_actionHomLeft, Category.assoc, h₂]

/-- Naturality of the interchange in the acted-on object. -/
lemma actionSwap_naturality (s t : C) {X Y : D} (f : X ⟶ Y) :
    t ⊴ₗ s ⊴ₗ f ≫ actionSwap s t Y = actionSwap s t X ≫ s ⊴ₗ t ⊴ₗ f := by
  have h₁ : t ⊴ₗ s ⊴ₗ f ≫ (αₗ t s Y).inv =
      (αₗ t s X).inv ≫ (t ⊗ s) ⊴ₗ f := by
    simp
  have h₂ : (s ⊗ t) ⊴ₗ f ≫ (αₗ s t Y).hom =
      (αₗ s t X).hom ≫ s ⊴ₗ t ⊴ₗ f := by
    simp
  simp only [actionSwap, Category.assoc]
  rw [reassoc_of% h₁, action_exchange_assoc, h₂]

/-- The interchange respects the original action unit. -/
lemma actionSwap_unitality (s : C) (X : D) :
    (λₗ[C] (s ⊙ₗ X)).hom = actionSwap s (𝟙_ C) X ≫ s ⊴ₗ (λₗ[C] X).hom := by
  simp only [actionSwap, Category.assoc]
  rw [← rightUnitor_actionHom, ← comp_actionHomLeft, braiding_rightUnitor,
    leftUnitor_actionHom, Iso.inv_hom_id_assoc]

/-- In a braided action, translating the acted-on category is genuinely
linear, with the canonical action interchange as lineator. -/
instance actionLeftLinear (s : C) : (actionLeft D s).LaxLeftLinear C where
  μₗ t X := actionSwap s t X
  μₗ_naturality_left f X := actionSwap_naturality_actor s f X
  μₗ_naturality_right t _ _ f := actionSwap_naturality s t f
  μₗ_associativity t r X := actionSwap_associativity s t r X
  μₗ_unitality X := actionSwap_unitality s X

end CategoryTheory.MonoidalCategory.MonoidalLeftAction
