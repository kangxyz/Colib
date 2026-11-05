/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.KTheory.Waldhausen.Additivity.Conditional

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Additivity
open scoped Simplicial Topology
universe u v

example (comparison : SSet.OrdinalSubdivision.RealizationComparison.{u})
    (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    (comparison.horizontalRealizationHomotopyEquiv X).toFun =
      (SSet.toTop.map (SSet.diagonalMap
        (SSet.OrdinalSubdivision.horizontalEndpoint X))).hom := rfl

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (comparison : SSet.OrdinalSubdivision.RealizationComparison.{max u v})
variable (V : Structure C) (W : Structure D) [HasBinaryCoproducts D]
variable {F G H : C ⥤ D} (a : F ⟶ G) (b : G ⟶ H)
variable (hs : IsCofibrationSequence V W a b)
include comparison

example (n : ℕ) :
    (Conditional.subdivisionPiEquiv comparison V n).toMonoidHom = subdivisionPiMap V n := rfl

example (n : ℕ) : Function.Surjective (subdivisionPiMap V n) :=
  Conditional.subdivisionPiMap_surjective comparison V n

example (n : ℕ) :
    KMap hs.exactG n = KMap (sumFunctor_isExact V W hs.exactH hs.exactF) n :=
  Conditional.KMap_additivity comparison V W a b hs n
