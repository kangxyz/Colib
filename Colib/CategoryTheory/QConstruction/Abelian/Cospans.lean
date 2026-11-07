/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.QConstruction.Abelian.Surjections

/-!
# Actual abelian Q-arrows: Cospans

Adapted from `Quillen/CategoryTheory/QConstruction/Abelian/Cospans.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual span maps,
universes and epi/mono hypotheses are retained. Bicartesian implications
use Stacks 08N4 directly.
-/

@[expose] public noncomputable section

universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped ZeroObject
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.QConstruction
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The actual admissible pullback span of a mono-epi cospan. -/
def cospanSpan {X Y U : C} (i : X ⟶ U) (p : Y ⟶ U) [Mono i] [Epi p] :
    AbelianSpan X Y :=
  ⟨pullback i p, pullback.fst i p, pullback.snd i p,
    (abelianExactStructure_deflation_iff C _).2 inferInstance,
    (abelianExactStructure_inflation_iff C _).2 inferInstance⟩

@[simp]
theorem mkHom_cospanSpan {X Y U : C} (i : X ⟶ U) (p : Y ⟶ U)
    [Mono i] [Epi p] :
    mkHom _ _ (cospanSpan i p) = inflationArrow i ≫ surjectionArrow p := by
  unfold inflationArrow surjectionArrow
  rw [← mkHom_comp]
  refine mkHom_eq_of_apexIso _ _ _ _ ?_ ?_ ?_
  · exact Iso.refl (pullback i p)
  · simp [cospanSpan, Span.comp]
  · simp [cospanSpan, Span.comp]

/-- Equality of cospan arrows supplies a compatible codomain isomorphism. -/
theorem exists_cospanIso_of_eq {X Y U V : C}
    (i : X ⟶ U) (p : Y ⟶ U) (j : X ⟶ V) (q : Y ⟶ V)
    [Mono i] [Epi p] [Mono j] [Epi q]
    (h : inflationArrow i ≫ surjectionArrow p = inflationArrow j ≫ surjectionArrow q) :
    ∃ e : U ≅ V, i ≫ e.hom = j ∧ p ≫ e.hom = q := by
  rw [← mkHom_cospanSpan, ← mkHom_cospanSpan] at h
  obtain ⟨e, hl, hr⟩ := (mkHom_eq_iff_apexIso _ _ _ _).1 h
  change e.hom ≫ pullback.fst j q = pullback.fst i p at hl
  change e.hom ≫ pullback.snd j q = pullback.snd i p at hr
  have w : pullback.fst i p ≫ j = pullback.snd i p ≫ q := by
    rw [← hl, Category.assoc, pullback.condition, ← Category.assoc, hr]
  have w' : pullback.fst j q ≫ i = pullback.snd j q ≫ p := by
    apply (cancel_epi e.hom).1
    simp only [← Category.assoc, hl, hr]
    exact pullback.condition
  let s := (CommSq.IsPullback.epi_to_isPushout (IsPullback.of_hasPullback i p).flip).1.flip
  let t := (CommSq.IsPullback.epi_to_isPushout (IsPullback.of_hasPullback j q).flip).1.flip
  let a := s.desc j q w
  let b := t.desc i p w'
  refine ⟨⟨a, b, ?_, ?_⟩, s.inl_desc _ _ _, s.inr_desc _ _ _⟩
  · apply (cancel_epi p).1
    simp [a, b]
  · apply (cancel_epi q).1
    simp [a, b]

/-- A commuting codomain isomorphism preserves the represented Q-arrow. -/
theorem cospan_eq_of_iso {X Y U V : C}
    (i : X ⟶ U) (p : Y ⟶ U) (j : X ⟶ V) (q : Y ⟶ V)
    [Mono i] [Epi p] [Mono j] [Epi q]
    (e : U ≅ V) (hi : i ≫ e.hom = j) (hp : p ≫ e.hom = q) :
    inflationArrow i ≫ surjectionArrow p = inflationArrow j ≫ surjectionArrow q := by
  have w : pullback.fst i p ≫ j = pullback.snd i p ≫ q := by
    rw [← hi, ← hp, ← Category.assoc, pullback.condition, Category.assoc]
  have w' : pullback.fst j q ≫ i = pullback.snd j q ≫ p := by
    apply (cancel_mono e.hom).1
    simp only [Category.assoc, hi, hp]
    exact pullback.condition
  let a := pullback.lift (pullback.fst i p) (pullback.snd i p) w
  let b := pullback.lift (pullback.fst j q) (pullback.snd j q) w'
  let f : pullback i p ≅ pullback j q :=
    ⟨a, b, by apply pullback.hom_ext <;> simp [a, b],
      by apply pullback.hom_ext <;> simp [a, b]⟩
  rw [← mkHom_cospanSpan, ← mkHom_cospanSpan]
  apply mkHom_eq_of_apexIso _ _ _ _ f
  · simp [f, a, cospanSpan]
  · simp [f, a, cospanSpan]

/-- Complete classification of mono-epi cospan representatives. -/
theorem cospan_eq_iff_iso {X Y U V : C}
    (i : X ⟶ U) (p : Y ⟶ U) (j : X ⟶ V) (q : Y ⟶ V)
    [Mono i] [Epi p] [Mono j] [Epi q] :
    inflationArrow i ≫ surjectionArrow p = inflationArrow j ≫ surjectionArrow q ↔
      ∃ e : U ≅ V, i ≫ e.hom = j ∧ p ≫ e.hom = q := by
  constructor
  · exact exists_cospanIso_of_eq i p j q
  · rintro ⟨e, hi, hp⟩
    exact cospan_eq_of_iso i p j q e hi hp

/-- Every Q-arrow has an ordinary mono-epi cospan representative. -/
theorem exists_cospan {X Y : C}
    (f : of (abelianExactStructure C).deflation (abelianExactStructure C).inflation X ⟶
      of (abelianExactStructure C).deflation (abelianExactStructure C).inflation Y) :
    ∃ (U : C) (i : X ⟶ U) (p : Y ⟶ U) (_ : Mono i) (_ : Epi p),
      inflationArrow i ≫ surjectionArrow p = f := by
  obtain ⟨s, rfl⟩ := Quotient.exists_rep f
  exact ⟨pushout s.l s.r, pushout.inl s.l s.r, pushout.inr s.l s.r,
    inferInstance, inferInstance, span_cospan_factorization s⟩
end CategoryTheory.QConstruction
