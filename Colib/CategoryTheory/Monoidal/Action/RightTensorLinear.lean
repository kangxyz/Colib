/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Monoidal.Action.LinearComposition
public import Colib.CategoryTheory.Monoidal.TensorFunctor.Associativity
public import Colib.CategoryTheory.Grothendieck.EndofunctorTelescope

/-! # The actual linear structure on right tensoring and its iterates -/

/-!
Implementation provenance: adapted from `Quillen/Aglib/CategoryTheory/Monoidal/Action/RightTensorLinear.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original functors,
comparison maps, homotopies, hypotheses and universes are retained.
-/

@[expose] public section
open CategoryTheory MonoidalCategory Grothendieck
open scoped MonoidalLeftAction
universe u v
namespace CategoryTheory.MonoidalCategory.TranslationTelescope
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The inverse associator is the actual left lineator of right tensoring. -/
@[instance_reducible]
def rightTensorLinear (e : C) : (tensorRight e).LaxLeftLinear C where
  μₗ P X := (α_ P X e).inv
  μₗ_naturality_left f X := associator_inv_naturality_left f X e
  μₗ_naturality_right P _ _ f := associator_inv_naturality_middle P f e
  μₗ_associativity _ _ _ := pentagon_hom_inv_inv_inv_hom.symm
  μₗ_unitality X := leftUnitor_tensor_hom X e

/-- Iterate that specified lineator by genuine composition of linear functors. -/
@[instance_reducible]
def rightIterateLinear (e : C) : ∀ n : ℕ,
    (EndofunctorTelescope.iterate (tensorRight e) n).LaxLeftLinear C
  | 0 => Functor.LaxLeftLinear.identity
  | n + 1 => by
      letI := rightIterateLinear e n
      letI := rightTensorLinear e
      exact Functor.LaxLeftLinear.composition _ _

/-- The actual iterated lineator, with its chosen recursive linear structure. -/
def rightIterateLineator (e : C) (n : ℕ) (P X : C) :
    P ⊗ (EndofunctorTelescope.iterate (tensorRight e) n).obj X ⟶
      (EndofunctorTelescope.iterate (tensorRight e) n).obj (P ⊗ X) :=
  letI := rightIterateLinear e n
  Functor.LaxLeftLinear.μₗ (EndofunctorTelescope.iterate (tensorRight e) n) P X

/-- The recursion retains the original inverse associator at every step. -/
theorem rightIterateLineator_succ (e : C) (n : ℕ) (P X : C) :
    rightIterateLineator e (n + 1) P X =
      (α_ P ((EndofunctorTelescope.iterate (tensorRight e) n).obj X) e).inv ≫
        (tensorRight e).map (rightIterateLineator e n P X) := rfl

/-- The iterated lineator cancels the exact original telescope commuting map. -/
theorem rightIterateLineator_commuteIterate (e : C) (n : ℕ) (P X : C) :
    rightIterateLineator e n P X ≫
      (EndofunctorTelescope.commuteIterate (leftStep e P) n).app X = 𝟙 _ := by
  induction n with
  | zero =>
    change (𝟙 (P ⊗ X)) ≫ 𝟙 _ = 𝟙 _
    simp only [Category.id_comp]
  | succ n ih =>
    change ((α_ P ((EndofunctorTelescope.iterate (tensorRight e) n).obj X) e).inv ≫
      rightIterateLineator e n P X ▷ e) ≫
      (((EndofunctorTelescope.commuteIterate (leftStep e P) n).app X) ▷ e ≫
        (α_ P ((EndofunctorTelescope.iterate (tensorRight e) n).obj X) e).hom) = 𝟙 _
    simp only [Category.assoc]
    rw [← Category.assoc (rightIterateLineator e n P X ▷ e),
      ← comp_whiskerRight, ih, id_whiskerRight, Category.id_comp, Iso.inv_hom_id]

/-- The same original maps cancel in the reverse order. -/
theorem commuteIterate_rightIterateLineator (e : C) (n : ℕ) (P X : C) :
    (EndofunctorTelescope.commuteIterate (leftStep e P) n).app X ≫
      rightIterateLineator e n P X = 𝟙 _ := by
  induction n with
  | zero =>
    change (𝟙 (P ⊗ X)) ≫ 𝟙 _ = 𝟙 _
    simp only [Category.id_comp]
  | succ n ih =>
    change (((EndofunctorTelescope.commuteIterate (leftStep e P) n).app X) ▷ e ≫
      (α_ P ((EndofunctorTelescope.iterate (tensorRight e) n).obj X) e).hom) ≫
      ((α_ P ((EndofunctorTelescope.iterate (tensorRight e) n).obj X) e).inv ≫
        rightIterateLineator e n P X ▷ e) = 𝟙 _
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← comp_whiskerRight, ih, id_whiskerRight]


end CategoryTheory.MonoidalCategory.TranslationTelescope
