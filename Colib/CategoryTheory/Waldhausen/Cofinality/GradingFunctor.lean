/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Cofinality.Grading
public import Colib.CategoryTheory.Waldhausen.ExactFunctor

/-! # Exact functors pull back additive Waldhausen gradings

Implementation provenance: `Quillen/Waldhausen/Cofinality/ComplementMap.lean` and
`Quillen/Waldhausen/GrothendieckGroup/Functor.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Their identical grading pullbacks
have this single categorical owner, with the original object values and proofs.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
universe u v u' v' w
namespace CategoryTheory.Waldhausen.Cofinality

namespace Grading
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : Structure C} {V : Structure D} {G : Type w} [AddCommGroup G]
  (d : Grading V G) {F : C ⥤ D} (hF : IsExact W.cof W.weq V.cof V.weq F)

/-- Pullback uses only actual exactness, including the genuine zero image. -/
def comap : Grading W G where
  value X := d.value (F.obj X)
  zero := (d.weak ((hF.zero W.isZero).iso V.isZero).hom (V.weq_iso _ inferInstance)).trans d.zero
  weak f hf := d.weak (F.map f) (hF.weak f hf)
  pushout hi hQ := d.pushout (hF.cofibration _ hi) (hF.pushout hi hQ)

end Grading

end CategoryTheory.Waldhausen.Cofinality
