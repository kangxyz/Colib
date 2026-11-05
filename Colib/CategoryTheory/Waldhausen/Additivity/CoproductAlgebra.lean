/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Additivity.CofiberEndpoint

/-! # Coproduct algebra in a genuine Waldhausen category

Implementation provenance: `Quillen/Waldhausen/Additivity/CoproductAlgebra.lean`
at commit c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual maps, hypotheses and
universes are retained; no subdivision realization equivalence is assumed.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v

namespace CategoryTheory.Waldhausen.Additivity

variable {C : Type u} [Category.{v} C] (W : Structure C)
variable [HasBinaryCoproducts C]
include W

/-- A chosen binary coproduct is the actual pushout over the chosen zero. -/
theorem coprod_isPushout (X Y : C) :
    IsPushout (W.isZero.to_ X) (W.isZero.to_ Y)
      (coprod.inl : X ⟶ X ⨿ Y) coprod.inr := by
  have hX : W.isZero.isInitial.to X = W.isZero.to_ X := W.isZero.eq_of_src _ _
  have hY : W.isZero.isInitial.to Y = W.isZero.to_ Y := W.isZero.eq_of_src _ _
  simpa only [hX, hY] using
    IsPushout.of_is_coproduct' (coprodIsCoprod X Y) W.isZero.isInitial

/-- Coproduct inclusions are cofibrations. -/
theorem coprod_inl_cof (X Y : C) : W.cof (coprod.inl : X ⟶ X ⨿ Y) :=
  W.cof_pushout (W.cof_zero Y) (coprod_isPushout W X Y).flip

/-- Coproduct inclusions are cofibrations. -/
theorem coprod_inr_cof (X Y : C) : W.cof (coprod.inr : Y ⟶ X ⨿ Y) :=
  W.cof_pushout (W.cof_zero X) (coprod_isPushout W X Y)

/-- Changing the first summand is an actual cobase change. -/
theorem coprod_map_left_isPushout {X X' : C} (f : X ⟶ X') (Y : C) :
    IsPushout f (coprod.inl : X ⟶ X ⨿ Y) coprod.inl (coprod.map f (𝟙 Y)) := by
  have hs := coprod_isPushout W X' Y
  have h₀ : W.isZero.to_ X ≫ f = W.isZero.to_ X' := W.isZero.eq_of_src _ _
  have h₁ : (coprod.inr : Y ⟶ X ⨿ Y) ≫ coprod.map f (𝟙 Y) = coprod.inr := by simp
  rw [← h₀, ← h₁] at hs
  exact hs.of_left (by simp) (coprod_isPushout W X Y)

/-- Changing the second summand is an actual cobase change. -/
theorem coprod_map_right_isPushout (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    IsPushout g (coprod.inr : Y ⟶ X ⨿ Y) coprod.inr (coprod.map (𝟙 X) g) := by
  have hs := (coprod_isPushout W X Y').flip
  have h₀ : W.isZero.to_ Y ≫ g = W.isZero.to_ Y' := W.isZero.eq_of_src _ _
  have h₁ : (coprod.inl : X ⟶ X ⨿ Y) ≫ coprod.map (𝟙 X) g = coprod.inl := by simp
  rw [← h₀, ← h₁] at hs
  exact hs.of_left (by simp) (coprod_isPushout W X Y).flip

/-- Binary coproduct maps preserve cofibrations. -/
theorem coprod_map_cof {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y')
    (hf : W.cof f) (hg : W.cof g) : W.cof (coprod.map f g) := by
  have he : coprod.map f g = coprod.map f (𝟙 Y) ≫ coprod.map (𝟙 X') g := by
    apply coprod.hom_ext <;> simp
  rw [he]
  exact W.cof.comp_mem _ _ (W.cof_pushout hf (coprod_map_left_isPushout W f Y))
    (W.cof_pushout hg (coprod_map_right_isPushout W X' g))

/-- Binary coproduct maps preserve weak equivalences by actual gluing. -/
theorem coprod_map_weak {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y')
    (hf : W.weq f) (hg : W.weq g) : W.weq (coprod.map f g) :=
  W.gluing (𝟙 W.zero) f g (coprod.map f g) (W.cof_zero X) (W.cof_zero X')
    (coprod_isPushout W X Y) (coprod_isPushout W X' Y')
    (W.isZero.eq_of_src _ _) (W.isZero.eq_of_src _ _)
    (by simp) (by simp) (W.weq.id_mem _) hf hg

/-- A coproduct of genuine zero objects is a zero object. -/
theorem coprod_isZero {X Y : C} (hX : IsZero X) (hY : IsZero Y) : IsZero (X ⨿ Y) := by
  let : IsIso (W.isZero.to_ Y) := W.isZero.isIso hY _
  let : IsIso (coprod.inl : X ⟶ X ⨿ Y) := (coprod_isPushout W X Y).isIso_inl_of_isIso
  exact hX.of_iso (asIso (coprod.inl : X ⟶ X ⨿ Y)).symm

end CategoryTheory.Waldhausen.Additivity
