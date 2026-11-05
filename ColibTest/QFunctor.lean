/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.CategoryTheory.ExactCategory.Functor.QConstruction

/-!
# Q-functoriality regression tests

Actual span maps are tested before introducing composition assumptions. The
three categories have independent object and hom universes. Exact functors
supply mixed pullback preservation without an abelian or all-pullbacks assumption.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory

universe v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

section Compatible

variable {C : Type u₁} {D : Type u₂} {T : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} T]
  {dC iC : MorphismProperty C} {dD iD : MorphismProperty D} {dT iT : MorphismProperty T}
  (F : QConstruction.CompatibleFunctor dC iC dD iD)
  (G : QConstruction.CompatibleFunctor dD iD dT iT)

example {X Y : C} (s : Span dC iC X Y) : (F.mapSpan s).apex = F.toFunctor.obj s.apex := rfl

example {X Y : C} (s : Span dC iC X Y) : (F.mapSpan s).l = F.toFunctor.map s.l := rfl

example {X Y : C} (s : Span dC iC X Y) : (F.mapSpan s).r = F.toFunctor.map s.r := rfl

example {X Y : C} {s t : Span dC iC X Y} (e : s ≅ t) :
    F.mapSpan s ≅ F.mapSpan t := F.mapSpanIso e

variable [dC.ContainsIdentities] [iC.ContainsIdentities]
  [dC.IsStableUnderComposition] [iC.IsStableUnderComposition]
  [dC.HasPullbacksAgainst iC] [dC.IsStableUnderBaseChangeAgainst iC]
  [iC.IsStableUnderBaseChangeAgainst dC]
  [dD.ContainsIdentities] [iD.ContainsIdentities]
  [dD.IsStableUnderComposition] [iD.IsStableUnderComposition]
  [dD.HasPullbacksAgainst iD] [dD.IsStableUnderBaseChangeAgainst iD]
  [iD.IsStableUnderBaseChangeAgainst dD]
  [dT.ContainsIdentities] [iT.ContainsIdentities]
  [dT.IsStableUnderComposition] [iT.IsStableUnderComposition]
  [dT.HasPullbacksAgainst iT] [dT.IsStableUnderBaseChangeAgainst iT]
  [iT.IsStableUnderBaseChangeAgainst dT]

example {X Y : C} (s : Span dC iC X Y) :
    F.mapQ.map (QConstruction.mkHom dC iC s) =
      QConstruction.mkHom dD iD (F.mapSpan s) := by
  simp

example (X : C) : F.mapSpan (Span.id X) ≅ Span.id (F.toFunctor.obj X) := F.mapSpanIdIso X

example {X Y Z : C} (s : Span dC iC X Y) (t : Span dC iC Y Z) :
    F.mapSpan (Span.comp s t) ≅ Span.comp (F.mapSpan s) (F.mapSpan t) :=
  F.mapSpanCompIso s t

example : (QConstruction.CompatibleFunctor.id dC iC).mapQ = 𝟭 (QConstruction dC iC) := by
  simp

example : (F.comp G).mapQ = F.mapQ ⋙ G.mapQ := by simp

end Compatible

section Exact

variable {C : Type u₁} {D : Type u₂} {T : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} T]
  [Preadditive C] [Preadditive D] [Preadditive T]
  [HasFiniteBiproducts C] [HasFiniteBiproducts D] [HasFiniteBiproducts T]
  {E : ExactStructure C} {E' : ExactStructure D} {E'' : ExactStructure T}
  (F : ExactFunctor E E') (G : ExactFunctor E' E'')

example : F.toQCompatibleFunctor.toFunctor = F.toFunctor := rfl

example {A B Z : C} (i : A ⟶ Z) (p : B ⟶ Z) (hi : E.inflation i) (hp : E.deflation p) :
    PreservesLimit (cospan i p) F.toQCompatibleFunctor.toFunctor :=
  F.toQCompatibleFunctor.preserves_mixed i p hi hp

example (X : C) : F.mapQ.obj (QConstruction.of E.deflation E.inflation X) =
    QConstruction.of E'.deflation E'.inflation (F.toFunctor.obj X) := by
  simp

example {X Y : C} (s : Span E.deflation E.inflation X Y) :
    F.mapQ.map (QConstruction.mkHom E.deflation E.inflation s) =
      QConstruction.mkHom E'.deflation E'.inflation (F.toQCompatibleFunctor.mapSpan s) :=
  F.mapQ_mkHom s

example : (ExactFunctor.id E).mapQ = 𝟭 (QConstruction E.deflation E.inflation) := by simp

example : (F.comp G).mapQ = F.mapQ ⋙ G.mapQ := by simp

end Exact
