/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References

public import Colib.KTheory.Waldhausen.Additivity.GroupMultiplication
public import Colib.KTheory.Waldhausen.Additivity.Basic

/-! # Literal multiplication formulas for canonical Waldhausen K-maps

The actual K-group law is commutative in every degree, including K₀.
Coproduct and structural cofibration sequences induce its literal existing
multiplication through the original canonical functorial K-maps.
-/
/-! Source: `Quillen/Waldhausen/Additivity/GroupFormula.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual maps and universes are retained.
The S-product isomorphism is not a normalized or strict S-model comparison. -/
@[expose] public section

open CategoryTheory.Waldhausen.Product

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits
universe u v

namespace CategoryTheory.Waldhausen.Additivity
open CategoryTheory.Waldhausen.Product
variable {C D : Type u} [Category.{v} C] [Category.{v} D]

/-- The actual existing K-group multiplication is commutative, including K₀. -/
theorem K_mul_comm (W : Structure C) (n : ℕ) (a b : W.K n) : a * b = b * a := by
  let := hasBinaryCoproducts W
  have he : (a, b) = (1, b) * (a, 1) := by simp
  calc
    a * b = coproductKMap W n (a, b) := (coproductKMap_eq_mul W n a b).symm
    _ = b * a := by rw [he, map_mul, coproductKMap_one_left, coproductKMap_one_right]

/-- An explicit commutative-group structure extending exactly the existing
homotopy-group structure. This does not replace the group operations. -/
@[instance_reducible] def KCommGroup (W : Structure C) (n : ℕ) : CommGroup (W.K n) where
  toGroup := inferInstance
  mul_comm := K_mul_comm W n

variable (V : Structure C) (W : Structure D) [HasBinaryCoproducts D]
variable {F H : C ⥤ D}

/-- The actual coproduct exact functor induces literal group multiplication
of the two original K-maps, with no changed normalization. -/
theorem KMap_sum_apply
    (hH : IsExact V.cof V.weq W.cof W.weq H)
    (hF : IsExact V.cof V.weq W.cof W.weq F) (n : ℕ) (a : V.K n) :
    KMap (sumFunctor_isExact V W hH hF) n a = KMap hH n a * KMap hF n a := by
  have he := Product.KEquiv_pair_apply V W W hH hF n a
  have hi : (Product.KEquiv W W n).symm (KMap hH n a, KMap hF n a) =
      KMap (pair_exact V W W hH hF) n a := by
    apply (Product.KEquiv W W n).injective
    simpa only [MulEquiv.apply_symm_apply] using he.symm
  calc
    KMap (sumFunctor_isExact V W hH hF) n a =
        KMap (coproductFunctor_isExact W) n (KMap (pair_exact V W W hH hF) n a) :=
      DFunLike.congr_fun
        (KMap_comp_KMap (pair_exact V W W hH hF) (coproductFunctor_isExact W) n).symm a
    _ = coproductKMap W n (KMap hH n a, KMap hF n a) := by
      change _ = KMap (coproductFunctor_isExact W) n
        ((Product.KEquiv W W n).symm (KMap hH n a, KMap hF n a))
      rw [hi]
    _ = KMap hH n a * KMap hF n a := coproductKMap_eq_mul W n _ _

/-- Genuine cofibration-sequence additivity in the literal original group law,
in subobject-then-quotient order, for every degree including zero. -/
theorem KMap_additivity_mul {G : C ⥤ D} (a : F ⟶ G) (b : G ⟶ H)
    (hs : IsCofibrationSequence V W a b) (n : ℕ) (x : V.K n) :
    KMap hs.exactG n x = KMap hs.exactF n x * KMap hs.exactH n x := by
  rw [KMap_additivity V W a b hs n, KMap_sum_apply V W hs.exactH hs.exactF n x]
  exact K_mul_comm W n _ _

end CategoryTheory.Waldhausen.Additivity

attribute [colib_tag "COL-0219",
  colib_ref "WeibelKBook" "V, Additivity Theorem 1.2 and proof, page 2"
    "adaptation"
    "Original KMaps and existing multiplication, in subobject-then-quotient order"]
  CategoryTheory.Waldhausen.Additivity.KMap_additivity_mul
  CategoryTheory.Waldhausen.Additivity.KMap_sum_apply

attribute [colib_tag "COL-0212",
  colib_ref "WeibelKBook" "V, proof of Additivity Theorem 1.2, page 2"
    "adaptation"
    "Actual coproduct and projection maps yield the existing commutative law, including K-zero"]
  CategoryTheory.Waldhausen.Additivity.K_mul_comm
  CategoryTheory.Waldhausen.Additivity.KCommGroup
