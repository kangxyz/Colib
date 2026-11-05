/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.KTheory.Waldhausen.Additivity.SubdivisionGroupMap
import Colib.Topology.Homotopy.Equiv.AdjacentComposites

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Additivity
open scoped Simplicial Topology
universe u v
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (V : Structure C) (W : Structure D) {F : C ⥤ D}
variable (hF : IsExact V.cof V.weq W.cof W.weq F)

example (n : ℕ) :
    (diagonalPiEquiv W n).toMonoidHom.comp (diagonalKMap V W hF n) =
      (KMap hF n).comp (diagonalPiEquiv V n).toMonoidHom :=
  diagonalKMap_naturality V W hF n

example (n : ℕ) : Function.Bijective (diagonalPiEquiv V n) :=
  (diagonalPiEquiv V n).bijective

example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) (n : ℕ) :
    (HomotopyGroup.homeomorphPiEquiv e (y := e x) rfl n).toMonoidHom =
      HomotopyGroup.piMap n (e : C(X, Y)) rfl := rfl

variable [HasBinaryCoproducts D] {G H : C ⥤ D}
variable (a : F ⟶ G) (b : G ⟶ H) (hs : IsCofibrationSequence V W a b)

example (n : ℕ) :
    (KMap hs.exactG n).comp ((diagonalPiEquiv V n).toMonoidHom.comp (subdivisionPiMap V n)) =
      (KMap (sumFunctor_isExact V W hs.exactH hs.exactF) n).comp
        ((diagonalPiEquiv V n).toMonoidHom.comp (subdivisionPiMap V n)) :=
  subdividedKMap_additivity V W a b hs n
