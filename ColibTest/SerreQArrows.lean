/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.QConstruction.Abelian.ArrowLayers
public import Colib.CategoryTheory.QConstruction.Abelian.SpanFactorization
public import Colib.CategoryTheory.QConstruction.Abelian.SpanNaturality

/-! Regression clients for actual abelian Q-arrow representatives and maps. -/

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.QConstruction

universe u v
noncomputable section
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [Abelian C]

example {X Y : C} (s : AbelianSpan X Y) :
    surjectionArrow s.l ≫ inflationArrow s.r = mkHom _ _ s := span_factorization s

example {X Y : C} (s : AbelianSpan X Y) :
    inflationArrow (pushout.inl s.l s.r) ≫ surjectionArrow (pushout.inr s.l s.r) =
      mkHom _ _ s := span_cospan_factorization s

example {X Y U V : C} (i : X ⟶ U) (p : Y ⟶ U) (j : X ⟶ V) (q : Y ⟶ V)
    [Mono i] [Epi p] [Mono j] [Epi q] :
    inflationArrow i ≫ surjectionArrow p = inflationArrow j ≫ surjectionArrow q ↔
      ∃ e : U ≅ V, i ≫ e.hom = j ∧ p ≫ e.hom = q := cospan_eq_iff_iso i p j q

example {X Y : C} (p q : Y ⟶ X) [Epi p] [Epi q]
    (h : surjectionArrow p = surjectionArrow q) : p = q := surjectionArrow_injective p q h

example {X Y : C} (e : X ≅ Y) :
    surjectionArrow e.hom = ((abelianExactStructure C).qIsoOfIso e).inv :=
  surjectionArrow_eq_qIsoOfIso_inv e

example {X Y X' Y' : C} (s : AbelianSpan X Y) (t : AbelianSpan X' Y')
    (a : X ⟶ X') (b : Y ⟶ Y') (c : s.apex ⟶ t.apex) [Mono a] [Mono b]
    (sq : IsPullback s.l c a t.l) (hr : s.r ≫ b = c ≫ t.r) :
    mkHom _ _ s ≫ inflationArrow b = inflationArrow a ≫ mkHom _ _ t :=
  span_naturality_of_pullback s t a b c sq hr

example {X Y X' Y' : C} (s : AbelianSpan X Y) (t : AbelianSpan X' Y')
    (a : X' ⟶ X) (b : Y' ⟶ Y) (c : t.apex ⟶ s.apex) [Epi a] [Epi b]
    (hl : t.l ≫ a = c ≫ s.l) (sq : IsPullback t.r c b s.r) :
    mkHom _ _ s ≫ surjectionArrow b = surjectionArrow a ≫ mkHom _ _ t :=
  span_naturality_of_surjection_pullback s t a b c hl sq

example {X Y : C} (s : AbelianSpan X Y) [IsIso (mkHom _ _ s)] :
    IsIso s.l ∧ IsIso s.r := isIso_legs_of_isIso s

example (M : C) :
    ((abelianExactStructure C).qZero ⟶ of _ _ M) ≃ Subobject M :=
  zeroArrowSubobjectEquiv M
