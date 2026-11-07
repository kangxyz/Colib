/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Monoidal.TensorFunctor.Associativity
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
Adapted from `Quillen/Aglib/CategoryTheory/Monoidal/TensorFunctor/Factorization.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving the original
functors, associators and category universes.
 # Actual right-translation factorization isomorphisms -/

@[expose] public section
noncomputable section
open CategoryTheory MonoidalCategory
universe u v
namespace CategoryTheory.MonoidalCategory.TranslationTelescope
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Changing the right tensor parameter uses its original tensor-product isomorphism. -/
def rightParameterIso {P Q : C} (f : P ≅ Q) : tensorRight P ≅ tensorRight Q :=
  NatIso.ofComponents (fun X ↦ Iso.refl X ⊗ᵢ f) (by
    intro X Y g
    dsimp
    simpa using (whisker_exchange g f.hom).symm)

/-- The original associator compares two right steps to their tensor sum. -/
def rightTensorIso (P Q : C) : tensorRight P ⋙ tensorRight Q ≅ tensorRight (P ⊗ Q) :=
  NatIso.ofComponents (fun X ↦ α_ X P Q) (by intro X Y g; dsimp; simp)

variable [BraidedCategory C]

/-- A complementary tensor sum factors as right addition followed by left addition. -/
def rightSumFactorization (P Q : C) :
    tensorRight (P ⊗ Q) ≅ tensorRight Q ⋙ tensorLeft P :=
  NatIso.ofComponents
    (fun X ↦ (α_ X P Q).symm ≪≫ (β_ X P ⊗ᵢ Iso.refl Q) ≪≫ α_ P X Q)
    (by
      intro X Y g
      dsimp [MonoidalCategory.tensorIso]
      simp only [tensorHom_id,
        associator_inv_naturality_left_assoc, Category.assoc]
      rw [← comp_whiskerRight_assoc, BraidedCategory.braiding_naturality_left, comp_whiskerRight,
        Category.assoc, associator_naturality_middle])

end CategoryTheory.MonoidalCategory.TranslationTelescope
