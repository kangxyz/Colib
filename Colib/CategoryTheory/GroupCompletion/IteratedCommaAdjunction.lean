/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.CategoryTheory.GroupCompletion.IteratedComma
public import Colib.CategoryTheory.FiberedCategory.CocartesianComma

/-!
Implementation provenance:
`Quillen/CategoryTheory/GroupCompletion/IteratedCommaAdjunction.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # The genuine strict-fiber/comma adjunction for the iterated projection -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v'
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
namespace CategoryTheory.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]
attribute [local instance] firstCoordinateLeftAction

/-- The explicit group-completion entry factors through the genuine strict fiber. -/
theorem iteratedCommaEntry_factorization (X : D) :
    iteratedStrictFiberEntry X ⋙
      CategoryTheory.Fiber.toCostructured (iteratedSecondProjection (C := C)) ⟨X⟩ =
        iteratedCommaEntry X := rfl

variable [∀ X : D, (MonoidalLeftAction.actionRight C X).Faithful]
  [∀ (X Y : D) (f : X ⟶ Y), Mono f]

instance iteratedFiberInclusion_isRightAdjoint (b : ActionLocalization C D) :
    (CategoryTheory.Fiber.toCostructured iteratedSecondProjection b).IsRightAdjoint := by
  apply CategoryTheory.Fiber.toCostructured_isRightAdjoint_of_lifts
  intro U
  obtain ⟨x, f, hx, hf⟩ := exists_iteratedSecondProjectionLift U.left b U.hom
  let := hf
  exact ⟨x, hx, f, inferInstance⟩

/-- Cocartesian lifting supplies the actual left adjoint to the fiber inclusion. -/
def iteratedFiberCommaAdjunction (b : ActionLocalization C D) :
    Functor.leftAdjoint (CategoryTheory.Fiber.toCostructured iteratedSecondProjection b) ⊣
      CategoryTheory.Fiber.toCostructured iteratedSecondProjection b :=
  Adjunction.ofIsRightAdjoint _

end CategoryTheory.GroupCompletion.Localization
