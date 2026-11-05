/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.CategoryTheory.QConstruction.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

/-!
# Isomorphisms of the restricted-span Q-construction

Extracted from the purely categorical `QIsomorphisms` sections of
`Quillen/Topology/ClassifyingSpace/PointedFunctor.lean` and
`Quillen/KTheory/Map/CoherenceData.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The topology and K-group imports are
not needed for these six declarations; the canonical Mathlib span and pullback
isomorphisms are used directly.
All constructions retain the actual objects, span legs and canonical maps.
No balancedness, ambient abelian structure or arbitrary pullback hypothesis is added.
This module makes no assertion about classifying spaces or homotopy K-groups.
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

variable (deflation inflation : MorphismProperty C)
  [deflation.ContainsIdentities] [inflation.ContainsIdentities]
  [deflation.IsStableUnderComposition] [inflation.IsStableUnderComposition]
  [deflation.HasPullbacksAgainst inflation]
  [deflation.IsStableUnderBaseChangeAgainst inflation]
  [inflation.IsStableUnderBaseChangeAgainst deflation]

/-- The identity-left-leg span of an admissible arrow. -/
def QConstruction.isoSpan {X Y : C} (e : X ≅ Y) (he : inflation e.hom) :
    Span deflation inflation X Y where
  apex := X
  l := 𝟙 X
  r := e.hom
  wl := MorphismProperty.ContainsIdentities.id_mem X
  wr := he

set_option backward.isDefEq.respectTransparency false in
/-- The composite of the two spans associated to an isomorphism and its inverse
is isomorphic to the identity span, using the actual pullback projection. -/
def QConstruction.isoSpanCompIso {X Y : C} (e : X ≅ Y)
    (he : inflation e.hom) (hi : inflation e.inv) :
    Span.comp (QConstruction.isoSpan deflation inflation e he)
      (QConstruction.isoSpan deflation inflation e.symm hi) ≅ Span.id X := by
  let s := QConstruction.isoSpan deflation inflation e he
  let t := QConstruction.isoSpan deflation inflation e.symm hi
  letI : HasPullback s.r t.l := inferInstance
  letI : IsIso t.l := inferInstanceAs (IsIso (𝟙 Y))
  letI : IsIso (pullback.fst s.r t.l) :=
    (IsPullback.of_hasPullback s.r t.l).isIso_fst_of_isIso
  refine Span.mkIso (asIso (pullback.fst s.r t.l)) ?_ ?_
  · simp [s, t, QConstruction.isoSpan, Span.comp]
  · change pullback.fst s.r t.l ≫ 𝟙 X = pullback.snd s.r t.l ≫ e.inv
    have h := pullback.condition (f := s.r) (g := t.l)
    change pullback.fst s.r t.l ≫ e.hom = pullback.snd s.r t.l ≫ 𝟙 Y at h
    dsimp only [s, t, QConstruction.isoSpan] at h ⊢
    simpa only [Category.assoc, e.hom_inv_id, Category.comp_id, Category.id_comp]
      using congrArg (fun k => k ≫ e.inv) h


/-- An original-category isomorphism, with admissible forward and inverse maps,
induces an isomorphism of Q-objects. -/
def QConstruction.isoOfIso {X Y : C} (e : X ≅ Y)
    (he : inflation e.hom) (hi : inflation e.inv) :
    QConstruction.of deflation inflation X ≅ QConstruction.of deflation inflation Y where
  hom := QConstruction.mkHom deflation inflation (QConstruction.isoSpan deflation inflation e he)
  inv := QConstruction.mkHom deflation inflation
    (QConstruction.isoSpan deflation inflation e.symm hi)
  hom_inv_id := Quotient.sound ⟨QConstruction.isoSpanCompIso deflation inflation e he hi⟩
  inv_hom_id := Quotient.sound ⟨QConstruction.isoSpanCompIso deflation inflation e.symm hi he⟩

/-- The Q-isomorphism of a reflexive original isomorphism is reflexive. -/
@[simp]
theorem QConstruction.isoOfIso_refl (X : C) (he hi : inflation (𝟙 X)) :
    QConstruction.isoOfIso deflation inflation (Iso.refl X) he hi =
      Iso.refl (QConstruction.of deflation inflation X) := by
  apply Iso.ext
  rfl


set_option backward.isDefEq.respectTransparency false in
/-- Multiplying the identity-left-leg spans of two isomorphisms gives the span
of their composite, up to the canonical pullback-apex isomorphism. -/
def QConstruction.isoSpanCompToIso {X Y Z : C} (e : X ≅ Y) (f : Y ≅ Z)
    (he : inflation e.hom) (hf : inflation f.hom) (hef : inflation (e ≪≫ f).hom) :
    Span.comp (QConstruction.isoSpan deflation inflation e he)
      (QConstruction.isoSpan deflation inflation f hf) ≅
        QConstruction.isoSpan deflation inflation (e ≪≫ f) hef := by
  let s := QConstruction.isoSpan deflation inflation e he
  let t := QConstruction.isoSpan deflation inflation f hf
  letI : HasPullback s.r t.l := inferInstance
  letI : IsIso t.l := inferInstanceAs (IsIso (𝟙 Y))
  letI : IsIso (pullback.fst s.r t.l) :=
    (IsPullback.of_hasPullback s.r t.l).isIso_fst_of_isIso
  refine Span.mkIso (asIso (pullback.fst s.r t.l)) ?_ ?_
  · simp [s, t, QConstruction.isoSpan, Span.comp]
  · change pullback.fst s.r t.l ≫ (e.hom ≫ f.hom) = pullback.snd s.r t.l ≫ f.hom
    have h := pullback.condition (f := s.r) (g := t.l)
    dsimp only [s, t, QConstruction.isoSpan] at h ⊢
    simpa only [Category.assoc, Category.comp_id] using congrArg (fun k => k ≫ f.hom) h

/-- The Q-isomorphism construction preserves composition. -/
theorem QConstruction.isoOfIso_trans {X Y Z : C} (e : X ≅ Y) (f : Y ≅ Z)
    (he : inflation e.hom) (he' : inflation e.inv)
    (hf : inflation f.hom) (hf' : inflation f.inv)
    (hef : inflation (e ≪≫ f).hom) (hef' : inflation (e ≪≫ f).inv) :
    QConstruction.isoOfIso deflation inflation (e ≪≫ f) hef hef' =
      QConstruction.isoOfIso deflation inflation e he he' ≪≫
        QConstruction.isoOfIso deflation inflation f hf hf' := by
  apply Iso.ext
  symm
  exact Quotient.sound ⟨QConstruction.isoSpanCompToIso deflation inflation e f he hf hef⟩


end CategoryTheory

attribute [colib_tag "COL-0046",
  colib_ref "WeibelKBook" "IV, Subobjects 6.1.2, isomorphism correspondence, forward direction"
    "generalization"
    "Forward Q-isomorphisms with explicit admissibility of both original directions"]
  CategoryTheory.QConstruction.isoOfIso
  CategoryTheory.QConstruction.isoOfIso_refl
  CategoryTheory.QConstruction.isoOfIso_trans
