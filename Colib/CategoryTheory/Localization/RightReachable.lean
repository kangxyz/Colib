/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Localization.RightRoofs
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
Implementation provenance: `Quillen/Aglib/CategoryTheory/Localization/RightReachable.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# The actual component detected by common right roofs -/
@[expose] public section
noncomputable section
open CategoryTheory
universe u v
namespace CategoryTheory.Localization
variable {C : Type u} [Category.{v} C]

/-- Objects admitting a common right target with the distinguished object. -/
def RightReachable (z : C) : ObjectProperty C :=
  fun X => ∃ Y : C, Nonempty (X ⟶ Y) ∧ Nonempty (z ⟶ Y)

theorem rightReachable_self (z : C) : RightReachable z z :=
  ⟨z, ⟨𝟙 z⟩, ⟨𝟙 z⟩⟩

variable (hsquare : ∀ {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z),
  ∃ W, ∃ p : Y ⟶ W, ∃ q : Z ⟶ W, f ≫ p = g ≫ q)

include hsquare in
/-- This property is invariant across every original arrow, not only across isomorphisms. -/
theorem rightReachable_arrow_iff (z : C) {X Y : C} (f : X ⟶ Y) :
    RightReachable z X ↔ RightReachable z Y := by
  constructor
  · rintro ⟨Z, ⟨p⟩, ⟨q⟩⟩
    obtain ⟨W, r, s, _⟩ := hsquare p f
    exact ⟨W, ⟨s⟩, ⟨q ≫ r⟩⟩
  · rintro ⟨Z, ⟨p⟩, ⟨q⟩⟩
    exact ⟨Z, ⟨f ≫ p⟩, ⟨q⟩⟩

attribute [local instance] CategoryTheory.Localization.groupoid
include hsquare in
/-- The roof condition is exactly membership in the original localization component. -/
theorem rightReachable_iff_localized_hom (z X : C) :
    RightReachable z X ↔
      Nonempty ((⊤ : MorphismProperty C).Q.obj z ⟶ (⊤ : MorphismProperty C).Q.obj X) := by
  constructor
  · rintro ⟨Y, ⟨p⟩, ⟨q⟩⟩
    exact ⟨(⊤ : MorphismProperty C).Q.map q ≫ inv ((⊤ : MorphismProperty C).Q.map p)⟩
  · rintro ⟨f⟩
    obtain ⟨Y, p, q, _⟩ := exists_right_roof hsquare f
    exact ⟨Y, ⟨q⟩, ⟨p⟩⟩

end CategoryTheory.Localization
