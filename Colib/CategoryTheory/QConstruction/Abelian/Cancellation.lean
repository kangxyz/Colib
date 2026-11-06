/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.QConstruction.Basic
public import Mathlib.CategoryTheory.Abelian.CommSq

/-!
# Cancellation in the abelian Q-construction

Every arrow in the Q-construction of an abelian category is a monomorphism.
The proof descends an isomorphism between pullback representatives along the
epimorphic pullback projections. This will make inclusion comma categories
thin, a necessary part of their identification with the poset of layers.
-/
/-!
Implementation provenance: adapted from
`Quillen/CategoryTheory/QConstruction/Abelian/Cancellation.lean` at Quillen
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
Native Mathlib full subcategories, Colib exact structures,
restricted spans, actual realization maps and their universes are retained.
No extension-closure, uniform filtration bound, alternate K-model or Aglib import is added.
-/

@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section
universe v u
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
namespace CategoryTheory.QConstruction
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A representative Q-arrow from `X` to `Y`: a span with an admissible epimorphism to `X` and an
admissible monomorphism to `Y` in the abelian exact structure. -/
abbrev AbelianSpan (X Y : C) :=
  Span (abelianExactStructure C).deflation (abelianExactStructure C).inflation X Y

instance abelianSpan_epi {X Y : C} (s : AbelianSpan X Y) : Epi s.l :=
  (abelianExactStructure_deflation_iff C _).1 s.wl

instance abelianSpan_mono {X Y : C} (s : AbelianSpan X Y) : Mono s.r :=
  (abelianExactStructure_inflation_iff C _).1 s.wr

/-- An isomorphism between pullback composites descends to their first spans. -/
def cancelSpanIso {X Y Z : C} (s₁ s₂ : AbelianSpan X Y) (t : AbelianSpan Y Z)
    (e : (Span.comp s₁ t).apex ≅ (Span.comp s₂ t).apex)
    (hr : e.hom ≫ (Span.comp s₂ t).r = (Span.comp s₁ t).r) :
    s₁.apex ≅ s₂.apex := by
  have hr' : e.hom ≫ pullback.fst s₂.r t.l ≫ s₂.r =
      pullback.fst s₁.r t.l ≫ s₁.r := by
    rw [pullback.condition, pullback.condition]
    have hs : e.hom ≫ pullback.snd s₂.r t.l = pullback.snd s₁.r t.l := by
      apply (cancel_mono t.r).mp
      simpa [Span.comp, assoc] using hr
    simpa [assoc] using congrArg (fun k => k ≫ t.l) hs
  have hri' : e.inv ≫ pullback.fst s₁.r t.l ≫ s₁.r =
      pullback.fst s₂.r t.l ≫ s₂.r := by
    rw [← hr']
    simp
  have hh : kernel.ι (pullback.fst s₁.r t.l) ≫
      (e.hom ≫ pullback.fst s₂.r t.l) = 0 := by
    apply (cancel_mono s₂.r).mp
    rw [assoc, assoc, hr', ← assoc]
    simp
  have hi : kernel.ι (pullback.fst s₂.r t.l) ≫
      (e.inv ≫ pullback.fst s₁.r t.l) = 0 := by
    apply (cancel_mono s₁.r).mp
    rw [assoc, assoc, hri', ← assoc]
    simp
  let h := Abelian.epiDesc (pullback.fst s₁.r t.l)
    (e.hom ≫ pullback.fst s₂.r t.l) hh
  let i := Abelian.epiDesc (pullback.fst s₂.r t.l)
    (e.inv ≫ pullback.fst s₁.r t.l) hi
  exact
    { hom := h
      inv := i
      hom_inv_id := by
        apply (cancel_epi (pullback.fst s₁.r t.l)).mp
        dsimp [h, i]
        rw [← assoc, Abelian.comp_epiDesc, assoc, Abelian.comp_epiDesc]
        simp
      inv_hom_id := by
        apply (cancel_epi (pullback.fst s₂.r t.l)).mp
        dsimp [h, i]
        rw [← assoc, Abelian.comp_epiDesc, assoc, Abelian.comp_epiDesc]
        simp }

@[reassoc (attr := simp)]
lemma fst_cancelSpanIso_hom {X Y Z : C} (s₁ s₂ : AbelianSpan X Y) (t : AbelianSpan Y Z)
    (e : (Span.comp s₁ t).apex ≅ (Span.comp s₂ t).apex)
    (hr : e.hom ≫ (Span.comp s₂ t).r = (Span.comp s₁ t).r) :
    pullback.fst s₁.r t.l ≫ (cancelSpanIso s₁ s₂ t e hr).hom =
      e.hom ≫ pullback.fst s₂.r t.l := by
  dsimp [cancelSpanIso]
  exact Abelian.comp_epiDesc _ _ _

/-- Equality of two Q-arrows can be cancelled against a third Q-arrow on the right. -/
lemma mkHom_right_cancel {X Y Z : C} (s₁ s₂ : AbelianSpan X Y) (t : AbelianSpan Y Z)
    (h : mkHom _ _ s₁ ≫ mkHom _ _ t = mkHom _ _ s₂ ≫ mkHom _ _ t) :
    mkHom _ _ s₁ = mkHom _ _ s₂ := by
  obtain ⟨e, hl, hr⟩ := (mkHom_eq_iff_apexIso _ _ (Span.comp s₁ t) (Span.comp s₂ t)).1 h
  apply mkHom_eq_of_apexIso _ _ s₁ s₂ (cancelSpanIso s₁ s₂ t e hr)
  · apply (cancel_epi (pullback.fst s₁.r t.l)).mp
    simpa [Span.comp, ← assoc] using hl
  · apply (cancel_epi (pullback.fst s₁.r t.l)).mp
    rw [← assoc, fst_cancelSpanIso_hom, assoc, pullback.condition, pullback.condition]
    have hs : e.hom ≫ pullback.snd s₂.r t.l = pullback.snd s₁.r t.l := by
      apply (cancel_mono t.r).mp
      simpa [Span.comp, assoc] using hr
    simpa [assoc] using congrArg (fun k => k ≫ t.l) hs

/-- All arrows of an abelian Q-construction are monomorphisms. -/
instance abelianQ_mono {X Y : QConstruction (abelianExactStructure C).deflation
    (abelianExactStructure C).inflation} (f : X ⟶ Y) : Mono f where
  right_cancellation := by
    intro Z g h w
    induction f using Quotient.inductionOn with | _ t =>
    induction g using Quotient.inductionOn with | _ s₁ =>
    induction h using Quotient.inductionOn with | _ s₂ =>
    exact mkHom_right_cancel s₁ s₂ t w

end CategoryTheory.QConstruction
