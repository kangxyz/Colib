/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.CategoryTheory.Bicategory.IsoQuotient
public import Mathlib.CategoryTheory.Bicategory.Span.Basic

/-!
# The Q-style restricted-span category

This file constructs the category of admissible spans from the precise
pullback-calculus hypotheses. It does not assert that arbitrary morphism
properties form an exact structure. The proved adapter from exact categories
is provided separately by `CategoryTheory.ExactCategory.ExactStructure` and its subsequent adapters.

The left leg is the deflation (admissible epimorphism); the right leg is the
inflation (admissible monomorphism). Composition uses the actual categorical
pullback supplied by mathlib's restricted-span bicategory. Only the mixed
pullbacks are required, rather than all pullbacks in the category.

## Implementation provenance

Adapted from `Quillen/CategoryTheory/QConstruction/Basic.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The source `Quillen.Q` becomes
`CategoryTheory.QConstruction`. Its objects, restricted span representatives,
quotient relation, morphism-property assumptions and universes are unchanged.
The apex-isomorphism extraction uses Mathlib's `Span.SpanBicat.apexIso`.
-/
@[expose] public noncomputable section

universe v u

open CategoryTheory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
  (deflation inflation : MorphismProperty C)
  [deflation.ContainsIdentities] [inflation.ContainsIdentities]
  [deflation.IsStableUnderComposition] [inflation.IsStableUnderComposition]
  [deflation.HasPullbacksAgainst inflation]
  [deflation.IsStableUnderBaseChangeAgainst inflation]
  [inflation.IsStableUnderBaseChangeAgainst deflation]

/-- The category of restricted spans modulo apex isomorphism. Once the
properties are obtained from an exact structure, this is its Q-construction. -/
abbrev QConstruction := Bicategory.IsoQuotient (Span.SpanBicat C deflation inflation)

namespace QConstruction

/-- An original object, viewed as an object of the restricted-span category. -/
def of (X : C) : QConstruction deflation inflation := ⟨⟨X⟩⟩

/-- An admissible span determines a Q-morphism. -/
def mkHom {X Y : C} (s : Span deflation inflation X Y) :
    of deflation inflation X ⟶ of deflation inflation Y :=
  Bicategory.IsoQuotient.mkHom s

/-- Two span representatives determine the same arrow precisely when they
are isomorphic as spans. -/
theorem mkHom_eq_iff {X Y : C} (s t : Span deflation inflation X Y) :
    mkHom deflation inflation s = mkHom deflation inflation t ↔ Nonempty (s ≅ t) :=
  Quotient.eq

/-- Apex isomorphisms commuting with both legs yield equal Q-morphisms. -/
theorem mkHom_eq_of_apexIso {X Y : C} (s t : Span deflation inflation X Y)
    (e : s.apex ≅ t.apex) (hl : e.hom ≫ t.l = s.l) (hr : e.hom ≫ t.r = s.r) :
    mkHom deflation inflation s = mkHom deflation inflation t :=
  Bicategory.IsoQuotient.mkHom_eq_of_iso (Span.mkIso e hl hr)

/-- Identity arrows are represented by identity spans. -/
@[simp]
theorem mkHom_id (X : C) :
    mkHom deflation inflation (Span.id X) = 𝟙 (of deflation inflation X) := rfl

/-- Composition is represented by the genuine pullback composite. -/
@[simp]
theorem mkHom_comp {X Y Z : C} (s : Span deflation inflation X Y)
    (t : Span deflation inflation Y Z) :
    mkHom deflation inflation (Span.comp s t) =
      mkHom deflation inflation s ≫ mkHom deflation inflation t := rfl

omit [deflation.ContainsIdentities] [inflation.ContainsIdentities] in
/-- The representative used by composition has the expected pullback apex. -/
theorem comp_apex {X Y Z : C} (s : Span deflation inflation X Y)
    (t : Span deflation inflation Y Z) :
    (Span.comp s t).apex = Limits.pullback s.r t.l := rfl

/-- No further quotient relation is imposed: equality is precisely a
commuting isomorphism between apices. -/
theorem mkHom_eq_iff_apexIso {X Y : C} (s t : Span deflation inflation X Y) :
    mkHom deflation inflation s = mkHom deflation inflation t ↔
      ∃ e : s.apex ≅ t.apex, e.hom ≫ t.l = s.l ∧ e.hom ≫ t.r = s.r := by
  rw [mkHom_eq_iff]
  constructor
  · rintro ⟨e⟩
    exact ⟨Span.SpanBicat.apexIso e, e.hom.hom_l, e.hom.hom_r⟩
  · rintro ⟨e, hl, hr⟩
    exact ⟨Span.mkIso e hl hr⟩

end QConstruction
end CategoryTheory

attribute [colib_tag "COL-0035",
  colib_ref "WeibelKBook" "IV, Definition 6.1, equation (6.1.1)" "generalization"
    "Span isomorphism classes and pullback composition under mixed pullback-calculus hypotheses"]
  CategoryTheory.QConstruction
  CategoryTheory.QConstruction.mkHom_eq_iff_apexIso
  CategoryTheory.QConstruction.mkHom_comp
