/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.KTheory.Waldhausen.Additivity.Basic

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Additivity
open scoped Simplicial Topology
universe u v

example (X : SSet.{u}) :
    (SSet.OrdinalSubdivision.realizationComparison.equiv X).toFun =
      (SSet.toTop.map (SSet.OrdinalSubdivision.endpoint X)).hom :=
  SSet.OrdinalSubdivision.realizationComparison.forward X

example (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    (SSet.OrdinalSubdivision.horizontalRealizationHomotopyEquiv X).toFun =
      (SSet.toTop.map (SSet.diagonalMap
        (SSet.OrdinalSubdivision.horizontalEndpoint X))).hom := rfl

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (V : Structure C) (W : Structure D) [HasBinaryCoproducts D]
variable {F G H : C ⥤ D} (a : F ⟶ G) (b : G ⟶ H)
variable (hs : IsCofibrationSequence V W a b)

example (n : ℕ) :
    (subdivisionPiEquiv V n).toMonoidHom = subdivisionPiMap V n := rfl

example (n : ℕ) : Function.Surjective (subdivisionPiMap V n) :=
  subdivisionPiMap_surjective V n

example (n : ℕ) :
    diagonalKMap V W hs.exactG n =
      diagonalKMap V W (sumFunctor_isExact V W hs.exactH hs.exactF) n :=
  diagonalKMap_additivity V W a b hs n

example (n : ℕ) :
    KMap hs.exactG n = KMap (sumFunctor_isExact V W hs.exactH hs.exactF) n :=
  KMap_additivity V W a b hs n
