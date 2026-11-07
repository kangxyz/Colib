/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Localization.StructuredArrow

/-!
Implementation provenance: `Quillen/Aglib/CategoryTheory/Localization/RightRoofs.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Right roofs in the actual groupoid localization

Common right multiples alone put every finite localized zigzag into a roof
with a common target. No cancellation or equality criterion for roofs is
needed for this existence statement.
-/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory

namespace CategoryTheory.Localization
variable {C : Type u} [Category.{v} C]
attribute [local instance] CategoryTheory.Localization.groupoid

/-- Every actual localized arrow is a right roof if same-source arrows admit commuting squares. -/
theorem exists_right_roof
    (hsquare : ∀ {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z),
      ∃ W, ∃ p : Y ⟶ W, ∃ q : Z ⟶ W, f ≫ p = g ≫ q)
    {X Y : C} (a : (⊤ : MorphismProperty C).Q.obj X ⟶ (⊤ : MorphismProperty C).Q.obj Y) :
    ∃ Z, ∃ p : X ⟶ Z, ∃ q : Y ⟶ Z,
      a = (⊤ : MorphismProperty C).Q.map p ≫ inv ((⊤ : MorphismProperty C).Q.map q) := by
  let Q := (⊤ : MorphismProperty C).Q
  let P : StructuredArrow (Q.obj X) Q → Prop := fun b =>
    ∃ Z, ∃ p : X ⟶ Z, ∃ q : b.right ⟶ Z, b.hom = Q.map p ≫ inv (Q.map q)
  apply CategoryTheory.Localization.induction_structuredArrow Q ⊤ P ?_ ?_ ?_
    (StructuredArrow.mk a)
  · exact ⟨X, 𝟙 X, 𝟙 X, by simp⟩
  · intro Y₁ Y₂ f φ hφ
    obtain ⟨Z, p, q, hφ⟩ := hφ
    change φ = Q.map p ≫ inv (Q.map q) at hφ
    obtain ⟨W, r, s, hs⟩ := hsquare q f
    refine ⟨W, p ≫ r, s, ?_⟩
    change φ ≫ Q.map f = Q.map (p ≫ r) ≫ inv (Q.map s)
    apply (cancel_mono (Q.map s)).1
    calc
      (φ ≫ Q.map f) ≫ Q.map s = Q.map p ≫ inv (Q.map q) ≫ Q.map (f ≫ s) := by
        rw [hφ, Q.map_comp]
        simp only [Category.assoc]
      _ = Q.map p ≫ inv (Q.map q) ≫ Q.map (q ≫ r) := by rw [hs]
      _ = (Q.map (p ≫ r) ≫ inv (Q.map s)) ≫ Q.map s := by
        simp [Category.assoc]
  · intro Y₁ Y₂ w hw φ hφ
    obtain ⟨Z, p, q, hφ⟩ := hφ
    change φ = Q.map p ≫ inv (Q.map q) at hφ
    refine ⟨Z, p, w ≫ q, ?_⟩
    change φ ≫ (CategoryTheory.Localization.isoOfHom Q ⊤ w hw).inv =
      Q.map p ≫ inv (Q.map (w ≫ q))
    rw [hφ]
    simp [CategoryTheory.Localization.isoOfHom, Category.assoc]

end CategoryTheory.Localization
