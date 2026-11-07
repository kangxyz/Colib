/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category

/-!
Adapted from `Quillen/Aglib/CategoryTheory/Monoidal/TensorFunctor/Associativity.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving the original
functors, associators and category universes.
 # Associativity of left and right tensor functors

The original associator supplies the literal tensor-functor commutation
map and the composition isomorphism of left tensor functors.
-/
@[expose] public section

open CategoryTheory MonoidalCategory
universe u v
namespace CategoryTheory.MonoidalCategory.TranslationTelescope
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The original associator commutes left tensoring with one right-translation step. -/
def leftStep (e P : C) : tensorLeft P ⋙ tensorRight e ⟶ tensorRight e ⋙ tensorLeft P where
  app X := (α_ P X e).hom
  naturality X Y f := by dsimp; simp

/-- The original associator, as an isomorphism of left tensor functors. -/
def leftTensorIso (P Q : C) : tensorLeft (P ⊗ Q) ≅ tensorLeft Q ⋙ tensorLeft P :=
  NatIso.ofComponents (fun X => α_ P Q X) (by intro X Y f; dsimp; simp)

end CategoryTheory.MonoidalCategory.TranslationTelescope
