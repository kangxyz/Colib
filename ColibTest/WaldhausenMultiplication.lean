/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

import Colib.KTheory.Waldhausen.Additivity.GroupFormula

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Additivity
universe u v
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (V : Structure C) (W : Structure D)

example (a b : W.K 0) : a * b = b * a := K_mul_comm W 0 a b

example : (KCommGroup W 0).toGroup = (inferInstance : Group (W.K 0)) := rfl

example (n : ℕ) :
    (Product.KEquiv V W n).toMonoidHom =
      (KMap (Product.fst_exact V W) n).prod (KMap (Product.snd_exact V W) n) := rfl

variable [HasBinaryCoproducts D]

example (n : ℕ) (a b : W.K n) : coproductKMap W n (a, b) = a * b :=
  coproductKMap_eq_mul W n a b

variable {F G H : C ⥤ D}

example (hH : IsExact V.cof V.weq W.cof W.weq H)
    (hF : IsExact V.cof V.weq W.cof W.weq F) (x : V.K 0) :
    KMap (sumFunctor_isExact V W hH hF) 0 x = KMap hH 0 x * KMap hF 0 x :=
  KMap_sum_apply V W hH hF 0 x

example (a : F ⟶ G) (b : G ⟶ H) (hs : IsCofibrationSequence V W a b) (x : V.K 0) :
    KMap hs.exactG 0 x = KMap hs.exactF 0 x * KMap hs.exactH 0 x :=
  KMap_additivity_mul V W a b hs 0 x

example (a : F ⟶ G) (b : G ⟶ H) (hs : IsCofibrationSequence V W a b)
    (n : ℕ) (x : V.K n) :
    KMap hs.exactG n x = KMap hs.exactF n x * KMap hs.exactH n x :=
  KMap_additivity_mul V W a b hs n x
