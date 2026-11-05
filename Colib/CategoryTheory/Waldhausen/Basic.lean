/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Waldhausen categories

The data are a genuine zero object and two morphism classes. The axioms are
closure under identities and composition, inclusion of isomorphisms,
cofibrancy of every object, pushouts along cofibrations, and the gluing axiom.
No additivity, approximation, comparison, or localization theorem is a field.
Implementation provenance: adapted from `Quillen/Waldhausen/Basic.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
This isolated draft has not been compiled.

-/
@[expose] public section


noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Waldhausen

/-- A Waldhausen structure on a category, with a specified zero object. -/
structure Structure (C : Type u) [Category.{v} C] where
  /-- Specified zero object. -/
  zero : C
  /-- The specified object really is zero. -/
  isZero : IsZero zero
  /-- Cofibrations. -/
  cof : MorphismProperty C
  /-- Weak equivalences. -/
  weq : MorphismProperty C
  /-- Cofibrations form a subcategory. -/
  cof_multiplicative : cof.IsMultiplicative
  /-- Weak equivalences form a subcategory. -/
  weq_multiplicative : weq.IsMultiplicative
  /-- All isomorphisms are cofibrations. -/
  cof_iso : MorphismProperty.isomorphisms C ≤ cof
  /-- All isomorphisms are weak equivalences. -/
  weq_iso : MorphismProperty.isomorphisms C ≤ weq
  /-- Every object is cofibrant. -/
  cof_zero (X : C) : cof (isZero.to_ X)
  /-- Pushouts along cofibrations exist. -/
  pushout_exists {A B D : C} (i : A ⟶ B) (f : A ⟶ D) :
    cof i → ∃ (P : C) (g : B ⟶ P) (j : D ⟶ P), IsPushout i f g j
  /-- Cobase change of a cofibration is a cofibration. -/
  cof_pushout {A B D P : C} {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ P} {j : D ⟶ P} :
    cof i → IsPushout i f g j → cof j
  /-- A map of pushout diagrams along cofibrations preserves weak
  equivalences when all three input maps are weak equivalences. -/
  gluing {A B D P A' B' D' P' : C}
    {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ P} {j : D ⟶ P}
    {i' : A' ⟶ B'} {f' : A' ⟶ D'} {g' : B' ⟶ P'} {j' : D' ⟶ P'}
    (a : A ⟶ A') (b : B ⟶ B') (d : D ⟶ D') (p : P ⟶ P') :
    cof i → cof i' → IsPushout i f g j → IsPushout i' f' g' j' →
    i ≫ b = a ≫ i' → f ≫ d = a ≫ f' →
    g ≫ p = b ≫ g' → j ≫ p = d ≫ j' →
    weq a → weq b → weq d → weq p

attribute [instance] Structure.cof_multiplicative Structure.weq_multiplicative

/-- Maps out of any actual zero object are cofibrations. -/
theorem Structure.cof_of_isZero.{u₁, v₁} {C : Type u₁} [Category.{v₁} C]
    (W : Structure C) {Z X : C} (hZ : IsZero Z) (f : Z ⟶ X) : W.cof f := by
  let e := hZ.iso W.isZero
  have hf : f = e.hom ≫ W.isZero.to_ X := hZ.eq_of_src _ _
  rw [hf]
  exact W.cof.comp_mem _ _ (W.cof_iso _ inferInstance) (W.cof_zero _)

end CategoryTheory.Waldhausen

attribute [colib_tag "COL-0144",
  colib_ref "Waldhausen1985" "Sections 1.1-1.2, pp.320-321 and 326-327"
    "background" "Cofibration and weak-equivalence axioms with a specified zero object"]
  CategoryTheory.Waldhausen.Structure
  CategoryTheory.Waldhausen.Structure.cof_of_isZero
