/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.CategoryTheory.QConstruction.ObjectClass

/-!
# Exact split sequences, kernel pullbacks and Q-object classes

The target is an arbitrary groupoid, not an assumed commutative group.
No comparison with the fundamental group is asserted here.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped ZeroObject

universe u v w z

noncomputable section

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

example (X Y : C) : E.inflation (biprod.inl : X ⟶ X ⊞ Y) :=
  E.inflation_biprod_inl X Y

example (X Y : C) : E.inflation (biprod.inr : Y ⟶ X ⊞ Y) :=
  E.inflation_biprod_inr X Y

example (X Y : C) :
    E.conflation (ShortComplex.mk (biprod.inl : X ⟶ X ⊞ Y) biprod.snd (by simp)) :=
  E.conflation_biprod_inl_snd X Y

example (X Y : C) :
    E.conflation (ShortComplex.mk (biprod.inr : Y ⟶ X ⊞ Y) biprod.fst (by simp)) :=
  E.conflation_biprod_inr_fst X Y

example {S : ShortComplex C} (hf : E.inflation S.f)
    (hg : IsColimit (CokernelCofork.ofπ S.g S.zero)) : E.conflation S :=
  E.conflation_of_inflation_of_isCokernel hf hg

example {S : ShortComplex C} (hg : E.deflation S.g)
    (hf : IsLimit (KernelFork.ofι S.f S.zero)) : E.conflation S :=
  E.conflation_of_deflation_of_isKernel hg hf

example {S : ShortComplex C} (hS : E.conflation S)
    {A P : C} {a : P ⟶ A} {b : P ⟶ S.X₂} {i : A ⟶ S.X₃}
    (sq : IsPullback a b i S.g) :
    E.conflation (ShortComplex.mk (sq.lift 0 S.f (by simp [S.zero])) a (by simp)) :=
  E.conflation_pullback_same_kernel hS sq

example {S : ShortComplex C} (hS : E.conflation S) :
    IsPullback (0 : S.X₁ ⟶ 0) S.f (0 : 0 ⟶ S.X₃) S.g :=
  E.conflation_kernel_isPullback hS

example (X : E.QCategory) : E.fromZeroTotal X =
    QConstruction.mkHom E.deflation E.inflation
      { apex := X.obj.of, l := 0, r := 𝟙 _,
        wl := E.deflation_zero _, wr := E.inflation_id _ } := rfl

example {X Y : C} (i : X ⟶ Y) (hi : E.inflation i) : E.qInflation i hi =
    QConstruction.mkHom E.deflation E.inflation
      { apex := X, l := 𝟙 _, r := i, wl := E.deflation_id _, wr := hi } := rfl

example {X Y : C} (p : X ⟶ Y) (hp : E.deflation p) : E.qDeflation p hp =
    QConstruction.mkHom E.deflation E.inflation
      { apex := X, l := p, r := 𝟙 _, wl := hp, wr := E.inflation_id _ } := rfl

example {X Y : C} (p : X ⟶ Y) (hp : E.deflation p) :
    E.fromZeroTotal (QConstruction.of E.deflation E.inflation Y) ≫ E.qDeflation p hp =
      E.fromZeroTotal (QConstruction.of E.deflation E.inflation X) :=
  E.fromZeroTotal_qDeflation p hp

example {X Y : C} (i : X ⟶ Y) (hi : E.inflation i) :
    E.fromZero (QConstruction.of E.deflation E.inflation X) ≫ E.qInflation i hi =
      E.fromZero (QConstruction.of E.deflation E.inflation Y) := E.fromZero_qInflation i hi

example {S : ShortComplex C} (hS : E.conflation S) :
    E.fromZero (QConstruction.of E.deflation E.inflation S.X₃) ≫
        E.qDeflation S.g (E.deflation_of_conflation hS) =
      E.fromZeroTotal (QConstruction.of E.deflation E.inflation S.X₁) ≫
        E.qInflation S.f (E.inflation_of_conflation hS) := E.conflation_q_relation hS

variable {D : Type w} [Groupoid.{z} D] (F : E.QCategory ⥤ D)

example (X : C) : (E.qObjectClass F X).asHom =
    F.map (E.fromZeroTotal (QConstruction.of E.deflation E.inflation X)) ≫
      inv (F.map (E.fromZero (QConstruction.of E.deflation E.inflation X))) := rfl

example {S : ShortComplex C} (hS : E.conflation S) :
    E.qObjectClass F S.X₂ = E.qObjectClass F S.X₁ * E.qObjectClass F S.X₃ :=
  E.qObjectClass_conflation F hS

example (X Y : C) : Commute (E.qObjectClass F X) (E.qObjectClass F Y) :=
  E.qObjectClass_commute F X Y

example (X Y : C) : E.qObjectClass F (X ⊞ Y) =
    E.qObjectClass F X * E.qObjectClass F Y :=
  E.qObjectClass_conflation F (E.conflation_biprod_inl_snd X Y)
