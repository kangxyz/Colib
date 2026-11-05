/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.CategoryTheory.QConstruction.Basic
import Colib.CategoryTheory.ExactCategory.Basic

/-!
# Isomorphism quotient and Q-span regression tests

The bicategory retains three independent universes. Restricted spans retain
independent object and hom universes and only the specified mixed pullbacks.
The exact-structure specialization checks that its proved instances suffice.
-/

open CategoryTheory CategoryTheory.Limits

universe w v u

noncomputable section

section Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

example {X Y : B} (f g : X ⟶ Y) :
    Bicategory.IsoQuotient.mkHom f = Bicategory.IsoQuotient.mkHom g ↔ Nonempty (f ≅ g) :=
  Bicategory.IsoQuotient.mkHom_eq_iff f g

example {X Y : B} (f : X ⟶ Y) :
    (Bicategory.IsoQuotient.homSetoid X Y).r f f := ⟨Iso.refl f⟩

example {X Y Z : B} {f f' : X ⟶ Y} {g g' : Y ⟶ Z}
    (hf : Nonempty (f ≅ f')) (hg : Nonempty (g ≅ g')) :
    Nonempty (f ≫ g ≅ f' ≫ g') := Bicategory.IsoQuotient.comp_respects_iso hf hg

example (X Y : B) : Function.Surjective
    (Bicategory.IsoQuotient.mkHom : (X ⟶ Y) →
      (Bicategory.IsoQuotient.mk X ⟶ Bicategory.IsoQuotient.mk Y)) :=
  Bicategory.IsoQuotient.mkHom_surjective X Y

example {X Y : B} {f g : X ⟶ Y}
    (h : (Bicategory.IsoQuotient.homSetoid X Y).r f g) :
    (Bicategory.IsoQuotient.homSetoid X Y).r g f :=
  (Bicategory.IsoQuotient.homSetoid X Y).symm h

example {X Y : B} {f g h : X ⟶ Y}
    (hfg : (Bicategory.IsoQuotient.homSetoid X Y).r f g)
    (hgh : (Bicategory.IsoQuotient.homSetoid X Y).r g h) :
    (Bicategory.IsoQuotient.homSetoid X Y).r f h :=
  (Bicategory.IsoQuotient.homSetoid X Y).trans hfg hgh

end Bicategory

section Spans

variable {C : Type u} [Category.{v} C] (d i : MorphismProperty C)
  [d.ContainsIdentities] [i.ContainsIdentities]
  [d.IsStableUnderComposition] [i.IsStableUnderComposition]
  [d.HasPullbacksAgainst i] [d.IsStableUnderBaseChangeAgainst i]
  [i.IsStableUnderBaseChangeAgainst d]

example (X : C) : QConstruction.mkHom d i (Span.id X) = 𝟙 (QConstruction.of d i X) := by
  simp

example {X Y Z : C} (s : Span d i X Y) (t : Span d i Y Z) :
    QConstruction.mkHom d i (Span.comp s t) =
      QConstruction.mkHom d i s ≫ QConstruction.mkHom d i t := by
  simp

example {X Y Z : C} (s : Span d i X Y) (t : Span d i Y Z) :
    (Span.comp s t).apex = pullback s.r t.l := QConstruction.comp_apex d i s t

example {X Y : C} (s t : Span d i X Y) :
    QConstruction.mkHom d i s = QConstruction.mkHom d i t ↔
      ∃ e : s.apex ≅ t.apex, e.hom ≫ t.l = s.l ∧ e.hom ≫ t.r = s.r :=
  QConstruction.mkHom_eq_iff_apexIso d i s t

example {X Y : C} (s t : Span d i X Y) (e : s.apex ≅ t.apex)
    (hl : e.hom ≫ t.l = s.l) (hr : e.hom ≫ t.r = s.r) :
    QConstruction.mkHom d i s = QConstruction.mkHom d i t :=
  QConstruction.mkHom_eq_of_apexIso d i s t e hl hr

example {X Y : C} (s : Span d i X Y) :
    QConstruction.mkHom d i (Span.comp (Span.id X) s) = QConstruction.mkHom d i s := by
  simp

example {X Y Z : C} (s : Span d i X Y) (t : Span d i Y Z) :
    (Span.comp s t).l = pullback.fst s.r t.l ≫ s.l := rfl

example {X Y Z : C} (s : Span d i X Y) (t : Span d i Y Z) :
    (Span.comp s t).r = pullback.snd s.r t.l ≫ t.r := rfl

end Spans

section ExactStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactCategory.ExactStructure C)

example : Category (QConstruction E.deflation E.inflation) := inferInstance

example (X : C) :
    QConstruction.mkHom E.deflation E.inflation (Span.id X) =
      𝟙 (QConstruction.of E.deflation E.inflation X) := by
  simp

example {X Y Z : C} (s : Span E.deflation E.inflation X Y)
    (t : Span E.deflation E.inflation Y Z) :
    (Span.comp s t).apex = pullback s.r t.l :=
  QConstruction.comp_apex E.deflation E.inflation s t

example {X Y : C} (s t : Span E.deflation E.inflation X Y) :
    QConstruction.mkHom E.deflation E.inflation s =
      QConstruction.mkHom E.deflation E.inflation t ↔ Nonempty (s ≅ t) :=
  QConstruction.mkHom_eq_iff E.deflation E.inflation s t

end ExactStructure
