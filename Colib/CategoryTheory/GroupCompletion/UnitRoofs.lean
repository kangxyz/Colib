/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.UnitArrows
public import Colib.CategoryTheory.GroupCompletion.CommonDenominator
public import Colib.CategoryTheory.Localization.RightRoofs
public import Mathlib.CategoryTheory.Endomorphism

/-!
Implementation provenance: `Quillen/CategoryTheory/GroupCompletion/UnitRoofs.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Single-numerator normal forms for completed zero loops

Every loop at the zero pair in the actual groupoid localization is an original
single-coordinate automorphism loop, conjugated by the original zero-to-pair
arrow. The proof uses only the proved common-denominator squares and original
unit-arrow normal forms.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory MonoidalCategory
attribute [local instance] CategoryTheory.Localization.groupoid

namespace CategoryTheory.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [IsGroupoid C]

/-- The original localization functor to the actual groupoid completion. -/
abbrev completionFunctor := (⊤ : MorphismProperty (Localization C C)).Q

/-- A single-coordinate automorphism gives a based loop through its original zero-to-pair arrow. -/
def numeratorLoop {P : C} (g : P ⟶ P) :
    End ((completionFunctor (C := C)).obj ⟨𝟙_ C, 𝟙_ C⟩) :=
  (completionFunctor (C := C)).map (unitArrow (𝟙 P)) ≫
    (completionFunctor (C := C)).map (ActionLocalization.ofHom (𝟙 P, g)) ≫
      inv ((completionFunctor (C := C)).map (unitArrow (𝟙 P)))

/-- The original numerator loop is the roof of its two original zero-to-pair arrows. -/
lemma numeratorLoop_eq_roof {P : C} (g : P ⟶ P) :
    numeratorLoop g = (completionFunctor (C := C)).map (unitArrow g) ≫
      inv ((completionFunctor (C := C)).map (unitArrow (𝟙 P))) := by
  rw [unitArrow_factor g, Functor.map_comp]
  exact (Category.assoc _ _ _).symm

/-- Conjugating a numerator by an original isomorphism preserves the completed based loop. -/
lemma numeratorLoop_transport {P Q : C} (g : P ⟶ P) (f : P ⟶ Q) :
    numeratorLoop g = numeratorLoop (inv f ≫ g ≫ f) := by
  rw [numeratorLoop_eq_roof, numeratorLoop_eq_roof,
    ← unitArrow_postcomp g f f, ← unitArrow_diagonal f]
  simp [Functor.map_comp, Category.assoc]

/-- Translating both coordinates preserves the original completed numerator loop. -/
lemma numeratorLoop_translation {P : C} (g : P ⟶ P) (s : C) :
    numeratorLoop g = numeratorLoop (s ◁ g) := by
  rw [numeratorLoop_eq_roof, numeratorLoop_eq_roof, ← unitArrow_translation g s]
  have h := unitArrow_translation (𝟙 P) s
  rw [MonoidalCategory.whiskerLeft_id] at h
  rw [← h]
  simp [Functor.map_comp, Category.assoc]

variable [BraidedCategory C]

/-- Every actual completed loop at zero has a single original projective numerator. -/
theorem exists_numeratorLoop
    (a : End ((completionFunctor (C := C)).obj ⟨𝟙_ C, 𝟙_ C⟩)) :
    ∃ P : C, ∃ g : P ⟶ P, a = numeratorLoop g := by
  obtain ⟨⟨P, Q⟩, p, q, ha⟩ := CategoryTheory.Localization.exists_right_roof
    ActionLocalization.exists_common_right_multiple a
  obtain ⟨f, rfl⟩ := unitArrow_surjective P Q p
  obtain ⟨g, rfl⟩ := unitArrow_surjective P Q q
  refine ⟨P, f ≫ inv g, ?_⟩
  let L := completionFunctor (C := C)
  have hh : L.map (ActionLocalization.ofHom ((𝟙 P, f) : (P, P) ⟶ (P, Q))) ≫
      inv (L.map (ActionLocalization.ofHom ((𝟙 P, g) : (P, P) ⟶ (P, Q)))) =
        L.map (ActionLocalization.ofHom ((𝟙 P, f ≫ inv g) : (P, P) ⟶ (P, P))) := by
    let F := ActionLocalization.ofFunctor (C := C) (D := C × C) ⋙ L
    change F.map ((𝟙 P, f) : (P, P) ⟶ (P, Q)) ≫
      inv (F.map ((𝟙 P, g) : (P, P) ⟶ (P, Q))) =
        F.map ((𝟙 P, f ≫ inv g) : (P, P) ⟶ (P, P))
    have hi : @inv (C × C) _ (P, P) (P, Q) (𝟙 P, g) _ =
        ((𝟙 P, inv g) : (P, Q) ⟶ (P, P)) := by
      apply IsIso.inv_eq_of_hom_inv_id
      exact Prod.ext (by simp) (by simp)
    rw [← F.map_inv, ← F.map_comp, hi]
    congr 1
    simp
  rw [ha, unitArrow_factor f, unitArrow_factor g]
  simp only [Functor.map_comp, IsIso.inv_comp, Category.assoc]
  simpa only [numeratorLoop, Category.assoc] using
    congrArg (fun t => L.map (unitArrow (𝟙 P)) ≫ t ≫ inv (L.map (unitArrow (𝟙 P)))) hh

end CategoryTheory.GroupCompletion.Localization
