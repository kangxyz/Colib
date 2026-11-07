/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.Functoriality

/-!
Implementation provenance:
`Quillen/CategoryTheory/GroupCompletion/Monomorphisms.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Original monomorphisms in the action localization -/
@[expose] public section
universe u v u' v'
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
namespace CategoryTheory.GroupCompletion.ActionLocalization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]

/-- The original-morphism entrance preserves monomorphisms: a denominator
isomorphism witnessing equality after composition also witnesses equality
before composition, by cancellation in the original category. -/
instance ofHom_mono {X Y : D} (f : X ⟶ Y) [Mono f] : Mono (ofHom (C := C) f) where
  right_cancellation := by
    rintro Z ⟨g⟩ ⟨h⟩ w
    change mkHom g ≫ ofHom f = mkHom h ≫ ofHom f at w
    rw [mkHom_comp_ofHom, mkHom_comp_ofHom, mkHom_eq_iff] at w
    obtain ⟨e, he⟩ := w
    apply Quotient.sound
    refine ⟨e, ?_⟩
    apply (cancel_mono f).1
    simpa only [Category.assoc] using he

end CategoryTheory.GroupCompletion.ActionLocalization
