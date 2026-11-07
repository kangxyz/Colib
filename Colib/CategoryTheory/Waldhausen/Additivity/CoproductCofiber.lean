/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Additivity.SplitSequence
public import Colib.CategoryTheory.Waldhausen.Product.Structure

/-! # Actual coproducts of displayed cofiber sequences

The original product pushout and the proved exact sum functor supply the
actual coproduct cofiber square. Only the genuine original cofibrations and
original cofiber squares are inputs; no global pushout preservation is assumed.

Implementation provenance: `Quillen/Waldhausen/Additivity/CoproductCofiber.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
maps, hypotheses and independent object/hom universes are retained.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CategoryTheory.Waldhausen.Additivity
variable {C : Type u} [Category.{v} C] (W : Structure C) [HasBinaryCoproducts C]

/-- The actual coproduct of two displayed cofiber squares is a displayed cofiber square. -/
theorem coprod_cofiber_isPushout
    {A B Q A' B' Q' : C} {i : A ⟶ B} {i' : A' ⟶ B'} {q : B ⟶ Q} {q' : B' ⟶ Q'}
    (hi : W.cof i) (hi' : W.cof i')
    (hQ : IsPushout i (W.isZero.from_ A) q (W.isZero.to_ Q))
    (hQ' : IsPushout i' (W.isZero.from_ A') q' (W.isZero.to_ Q')) :
    IsPushout (coprod.map i i') (W.isZero.from_ (A ⨿ A'))
      (coprod.map q q') (W.isZero.to_ (Q ⨿ Q')) := by
  have hp := Product.product_isPushout
    (A := (A, A')) (B := (B, B')) (E := (W.zero, W.zero)) (P := (Q, Q'))
    (i, i') (W.isZero.from_ A, W.isZero.from_ A') (q, q')
    (W.isZero.to_ Q, W.isZero.to_ Q') hQ hQ'
  have he := Additivity.sumFunctor_isExact (Product.productStructure W W) W
    (Product.fst_exact W W) (Product.snd_exact W W)
  have hs := @IsExact.pushout (C × C) _ C _ _ _ _ _ _ he
    (A, A') (B, B') (W.zero, W.zero) (Q, Q')
    (i, i') (W.isZero.from_ A, W.isZero.from_ A') (q, q')
    (W.isZero.to_ Q, W.isZero.to_ Q') ⟨hi, hi'⟩ hp
  change IsPushout (coprod.map i i') (coprod.map (W.isZero.from_ A) (W.isZero.from_ A'))
    (coprod.map q q') (coprod.map (W.isZero.to_ Q) (W.isZero.to_ Q')) at hs
  let hz := Additivity.coprod_isZero W W.isZero W.isZero
  apply hs.of_iso (Iso.refl _) (Iso.refl _) (hz.iso W.isZero) (Iso.refl _)
  · simp
  · exact W.isZero.eq_of_tgt _ _
  · simp
  · exact hz.eq_of_src _ _

end CategoryTheory.Waldhausen.Additivity
