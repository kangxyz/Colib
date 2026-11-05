/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.CategoryTheory.ExactCategory.Functor.Pullbacks

/-!
# Matrix deflations and exact-functor pullback regression tests

The source and target object and hom universes are independent. No abelian
structure or ambient existence of arbitrary pullbacks is assumed. The signed
matrix has row `[-i, p]` and column `[a, b]` throughout.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.Preadditive

noncomputable section

universe v₁ v₂ u₁ u₂

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

section Matrix

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

example {A B T : C} (p : B ⟶ T) :
    IsPullback (biprod.snd : A ⊞ B ⟶ B) (biprod.map (𝟙 A) p)
      p (biprod.snd : A ⊞ T ⟶ T) :=
  ExactStructure.isPullback_biprod_map_right p

example {A B T : C} (f : A ⟶ T) (p : B ⟶ T) (hp : E.deflation p) :
    E.deflation (biprod.desc f p) := E.deflation_biprod_desc f p hp

example {A B T : C} (i : A ⟶ T) (p : B ⟶ T) (hp : E.deflation p) :
    E.deflation (biprod.desc (-i) p) := E.deflation_biprod_desc (-i) p hp

example {P A B T : C} {a : P ⟶ A} {b : P ⟶ B}
    {i : A ⟶ T} {p : B ⟶ T} (sq : IsPullback a b i p) :
    IsLimit (KernelFork.ofι (biprod.lift a b)
      (show biprod.lift a b ≫ biprod.desc (-i) p = 0 by
        simp only [biprod.lift_desc, comp_neg, sq.w, neg_add_cancel])) :=
  pullbackMatrixKernel sq

example {P A B T : C} {a : P ⟶ A} {b : P ⟶ B}
    {i : A ⟶ T} {p : B ⟶ T} (sq : IsPullback a b i p) (hp : E.deflation p) :
    E.conflation (ShortComplex.mk (biprod.lift a b) (biprod.desc (-i) p)
      (by simp only [biprod.lift_desc, comp_neg, sq.w, neg_add_cancel])) :=
  E.conflation_of_isKernel _ (pullbackMatrixKernel sq) (E.deflation_biprod_desc (-i) p hp)

end Matrix

section Functor

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  {E : ExactStructure C} {E' : ExactStructure D} (F : ExactFunctor E E')

example {P A B T : C} {a : P ⟶ A} {b : P ⟶ B}
    {i : A ⟶ T} {p : B ⟶ T} (sq : IsPullback a b i p) (hp : E.deflation p) :
    IsPullback (F.toFunctor.map a) (F.toFunctor.map b)
      (F.toFunctor.map i) (F.toFunctor.map p) :=
  F.map_isPullback sq hp

example {A B T : C} (i : A ⟶ T) (p : B ⟶ T) (hp : E.deflation p) :
    PreservesLimit (cospan i p) F.toFunctor := F.preserves_pullback i p hp

example {A B T : C} (i : A ⟶ T) (p : B ⟶ T) (hp : E.deflation p)
    [HasPullback i p] :
    IsPullback (F.toFunctor.map (pullback.fst i p))
      (F.toFunctor.map (pullback.snd i p)) (F.toFunctor.map i) (F.toFunctor.map p) :=
  F.map_isPullback (IsPullback.of_hasPullback i p) hp

end Functor
