/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.ActionLocalization
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
Implementation provenance: `Quillen/CategoryTheory/GroupCompletion/CommonDenominator.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Actual common denominators for action-localization arrows

A braided monoidal category acting on a groupoid gives common right multiples
for every pair of same-source arrows in its action localization. The square is
constructed from the original translating objects, their braiding, and the
actual action associators; no cancellation or fraction-presentation axiom is
assumed.
-/
@[expose] public section
noncomputable section
universe u v u' v'
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction

namespace CategoryTheory.GroupCompletion.ActionLocalization
variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalLeftAction C D] [IsGroupoid D]

/-- The actual map exchanging two successive translating objects. -/
def swapAction (s t : C) (X : D) : s ⊙ₗ (t ⊙ₗ X) ⟶ t ⊙ₗ (s ⊙ₗ X) :=
  (αₗ s t X).inv ≫ (β_ s t).hom ⊵ₗ X ≫ (αₗ t s X).hom

/-- The second side of the common-denominator square for two represented arrows. -/
def commonRightMap {X Y Z : D} (f : HomRep (C := C) X Y) (g : HomRep (C := C) X Z) :
    (⟨Z⟩ : ActionLocalization C D) ⟶ ⟨g.denom ⊙ₗ Y⟩ :=
  mkHom ⟨f.denom, f.denom ⊴ₗ inv g.map ≫
    swapAction f.denom g.denom X ≫ g.denom ⊴ₗ f.map⟩

/-- The displayed original arrows form a genuine commuting square in the action localization. -/
lemma commonRightMap_square {X Y Z : D}
    (f : HomRep (C := C) X Y) (g : HomRep (C := C) X Z) :
    mkHom f ≫ translation g.denom Y = mkHom g ≫ commonRightMap f g := by
  apply Quotient.sound
  refine ⟨(β_ f.denom g.denom).symm, ?_⟩
  simp [HomRep.comp, swapAction, Category.assoc,
    ← MonoidalLeftAction.actionHomRight_comp_assoc]

/-- Same-source arrows admit a common right multiple, without a cancellation axiom. -/
lemma exists_common_right_multiple {X Y Z : ActionLocalization C D} (f : X ⟶ Y) (g : X ⟶ Z) :
    ∃ W, ∃ p : Y ⟶ W, ∃ q : Z ⟶ W, f ≫ p = g ≫ q := by
  rcases X with ⟨X⟩
  rcases Y with ⟨Y⟩
  rcases Z with ⟨Z⟩
  obtain ⟨f, rfl⟩ := mkHom_surjective X Y f
  obtain ⟨g, rfl⟩ := mkHom_surjective X Z g
  exact ⟨⟨g.denom ⊙ₗ Y⟩, translation g.denom Y, commonRightMap f g,
    commonRightMap_square f g⟩

end CategoryTheory.GroupCompletion.ActionLocalization
