/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.DiagonalAction

/-!
Implementation provenance: `Quillen/CategoryTheory/GroupCompletion/UnitArrows.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Normal forms for original arrows from the zero pair

In a monoidal groupoid, an original arrow from the pair of units to `(P,Q)`
is represented canonically by its actual isomorphism from `P` to `Q`. This
retains the denominator and the right unitor, and makes simultaneous diagonal
automorphisms vanish after the original zero-to-pair arrow.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction

namespace CategoryTheory.GroupCompletion.ActionLocalization

/-- Postcomposition with an original category arrow keeps the original translating object. -/
lemma mkHom_postcomp {C : Type u} {D : Type*} [Category.{v} C] [Category* D]
    [MonoidalCategory C] [MonoidalLeftAction C D] {X Y Z : D}
    (f : HomRep (C := C) X Y) (g : Y ⟶ Z) :
    mkHom f ≫ ofHom g = mkHom ⟨f.denom, f.map ≫ g⟩ := by
  rw [mkHom_factorization f, mkHom_factorization ⟨f.denom, f.map ≫ g⟩,
    Category.assoc, ← ofHom_comp]

end CategoryTheory.GroupCompletion.ActionLocalization

namespace CategoryTheory.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [IsGroupoid C]

/-- The original arrow from the zero pair determined by an actual morphism `P ⟶ Q`. -/
def unitArrow {P Q : C} (f : P ⟶ Q) :
    (⟨𝟙_ C, 𝟙_ C⟩ : Localization C C) ⟶ ⟨P, Q⟩ :=
  mkHom P (ρ_ P).hom ((ρ_ P).hom ≫ f)

/-- Every represented arrow out of zero has the displayed canonical numerator form. -/
lemma mkHom_from_unit {P Q : C}
    (f : ActionLocalization.HomRep (C := C) (𝟙_ C, 𝟙_ C) (P, Q)) :
    ActionLocalization.mkHom f = unitArrow (inv f.map.1 ≫ f.map.2) := by
  apply Quotient.sound
  refine ⟨(ρ_ f.denom).symm ≪≫ asIso f.map.1, ?_⟩
  apply Prod.ext
  · change ((ρ_ f.denom).inv ≫ f.map.1) ▷ (𝟙_ C) ≫ (ρ_ P).hom = f.map.1
    rw [rightUnitor_naturality]
    simp
  · change ((ρ_ f.denom).inv ≫ f.map.1) ▷ (𝟙_ C) ≫
      (ρ_ P).hom ≫ inv f.map.1 ≫ f.map.2 = f.map.2
    rw [← Category.assoc, rightUnitor_naturality]
    simp

/-- Every original zero-to-pair arrow comes from an actual morphism of the two coordinates. -/
lemma unitArrow_surjective (P Q : C) :
    Function.Surjective (unitArrow : (P ⟶ Q) →
      ((⟨𝟙_ C, 𝟙_ C⟩ : Localization C C) ⟶ ⟨P, Q⟩)) := by
  intro a
  obtain ⟨f, rfl⟩ := ActionLocalization.mkHom_surjective _ _ a
  exact ⟨inv f.map.1 ≫ f.map.2, (mkHom_from_unit f).symm⟩

/-- Original postcomposition changes the numerator by the displayed two-coordinate conjugation. -/
lemma unitArrow_postcomp {P Q P' Q' : C} (f : P ⟶ Q) (a : P ⟶ P') (b : Q ⟶ Q') :
    unitArrow f ≫ ActionLocalization.ofHom (a, b) = unitArrow (inv a ≫ f ≫ b) := by
  change ActionLocalization.mkHom (X := (𝟙_ C, 𝟙_ C)) (Y := (P, Q))
    ⟨P, ((ρ_ P).hom, (ρ_ P).hom ≫ f)⟩ ≫ _ = _
  rw [ActionLocalization.mkHom_postcomp, mkHom_from_unit]
  congr 1
  change inv ((ρ_ P).hom ≫ a) ≫ ((ρ_ P).hom ≫ f) ≫ b = inv a ≫ f ≫ b
  simp [Category.assoc]

/-- Simultaneously applying the same isomorphism to both coordinates changes no zero arrow. -/
lemma unitArrow_diagonal {P Q : C} (g : P ⟶ Q) :
    unitArrow (𝟙 P) ≫ ActionLocalization.ofHom (g, g) = unitArrow (𝟙 Q) := by
  rw [unitArrow_postcomp]
  simp

/-- An original zero-to-pair arrow factors through its single second-coordinate numerator. -/
lemma unitArrow_factor {P Q : C} (f : P ⟶ Q) :
    unitArrow f = unitArrow (𝟙 P) ≫ ActionLocalization.ofHom (𝟙 P, f) := by
  rw [unitArrow_postcomp]
  simp

/-- Translating both coordinates transports the original numerator by the actual action. -/
lemma unitArrow_translation {P Q : C} (g : P ⟶ Q) (s : C) :
    unitArrow g ≫ ActionLocalization.translation s (P, Q) = unitArrow (s ◁ g) := by
  change ActionLocalization.mkHom (X := (𝟙_ C, 𝟙_ C)) (Y := (P, Q))
    ⟨P, ((ρ_ P).hom, (ρ_ P).hom ≫ g)⟩ ≫
      ActionLocalization.mkHom ⟨s, 𝟙 (s ⊙ₗ (P, Q))⟩ = _
  rw [← ActionLocalization.mkHom_comp, mkHom_from_unit]
  congr 1
  change inv ((α_ s P (𝟙_ C)).hom ≫ s ◁ (ρ_ P).hom ≫ 𝟙 _) ≫
    ((α_ s P (𝟙_ C)).hom ≫ s ◁ ((ρ_ P).hom ≫ g) ≫ 𝟙 _) = s ◁ g
  simp [Category.assoc]

/-- At the pair of units the canonical zero arrow is the original identity. -/
lemma unitArrow_unit : unitArrow (𝟙 (𝟙_ C)) = 𝟙 (⟨𝟙_ C, 𝟙_ C⟩ : Localization C C) := by
  have h := mkHom_from_unit (ActionLocalization.HomRep.id (C := C) (𝟙_ C, 𝟙_ C))
  change 𝟙 (⟨𝟙_ C, 𝟙_ C⟩ : Localization C C) =
    unitArrow (inv (λ_ (𝟙_ C)).hom ≫ (λ_ (𝟙_ C)).hom) at h
  simpa using h.symm

end CategoryTheory.GroupCompletion.Localization
