/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.ActionLocalization

/-!
Implementation provenance:
`Quillen/CategoryTheory/GroupCompletion/ActionTranslationNaturality.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Naturality of the original action-localization translation arrows

The common-denominator translation arrows intertwine the original category
maps with the translated maps. This supplies the successor squares for actual
finite-stage maps into the group-completion category.
-/
@[expose] public section

universe u v u' v'
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction

namespace CategoryTheory.GroupCompletion.ActionLocalization
variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [MonoidalCategory C] [MonoidalLeftAction C D]

/-- Translation intertwines a map with its original action translate. -/
@[reassoc]
lemma ofHom_translation (s : C) {X Y : D} (f : X ⟶ Y) :
    ofHom (C := C) f ≫ translation s Y =
      translation s X ≫ ofHom (s ⊴ₗ f) := by
  rw [← mkHom_factorization (⟨s, s ⊴ₗ f⟩ : HomRep X (s ⊙ₗ Y))]
  apply Quotient.sound
  refine ⟨ρ_ s, ?_⟩
  simp [HomRep.comp]

end CategoryTheory.GroupCompletion.ActionLocalization
