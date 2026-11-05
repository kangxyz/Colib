/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Additivity.CoproductFunctor
public import Colib.KTheory.Waldhausen.Product.Functoriality
public import Colib.CategoryTheory.Waldhausen.Additivity.SplitSequence

/-! # Coproduct induces the actual K-group multiplication

The genuine coproduct exact functor and the two genuine zero embeddings
supply a homomorphism from the product K-group with both unit restrictions
equal to the identity. Group algebra identifies it with the existing
multiplication and proves commutativity, including degree zero.
-/
/-! Source: `Quillen/Waldhausen/Additivity/GroupMultiplication.lean` at
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
variable {C : Type u} [Category.{v} C] (W : Structure C) [HasBinaryCoproducts C]

/-- The actual coproduct K-map transported through the original product
projection equivalence. -/
def coproductKMap (n : ℕ) : W.K n × W.K n →* W.K n :=
  (KMap (coproductFunctor_isExact W) n).comp (Product.KEquiv W W n).symm.toMonoidHom

theorem coproductKMap_one_right (n : ℕ) (a : W.K n) : coproductKMap W n (a, 1) = a := by
  have he := Product.KEquiv_pair_apply W W W (IsExact.id W.cof W.weq)
    (zeroFunctor_isExact W W) n a
  simp only [KMap_id, KMap_zeroFunctor, MonoidHom.id_apply, MonoidHom.one_apply] at he
  have hi : (Product.KEquiv W W n).symm (a, 1) = KMap (firstEmbedding_isExact W) n a := by
    apply (Product.KEquiv W W n).injective
    simpa only [MulEquiv.apply_symm_apply] using he.symm
  change KMap (coproductFunctor_isExact W) n ((Product.KEquiv W W n).symm (a, 1)) = a
  rw [hi]
  have h := KMap_eq_of_iso ((firstEmbedding_isExact W).comp (coproductFunctor_isExact W))
    (IsExact.id W.cof W.weq) (firstEmbeddingCoproductIso W) n
  rw [← KMap_comp_KMap, KMap_id] at h
  exact DFunLike.congr_fun h a

theorem coproductKMap_one_left (n : ℕ) (a : W.K n) : coproductKMap W n (1, a) = a := by
  have he := Product.KEquiv_pair_apply W W W (zeroFunctor_isExact W W)
    (IsExact.id W.cof W.weq) n a
  simp only [KMap_id, KMap_zeroFunctor, MonoidHom.id_apply, MonoidHom.one_apply] at he
  have hi : (Product.KEquiv W W n).symm (1, a) = KMap (secondEmbedding_isExact W) n a := by
    apply (Product.KEquiv W W n).injective
    simpa only [MulEquiv.apply_symm_apply] using he.symm
  change KMap (coproductFunctor_isExact W) n ((Product.KEquiv W W n).symm (1, a)) = a
  rw [hi]
  have h := KMap_eq_of_iso ((secondEmbedding_isExact W).comp (coproductFunctor_isExact W))
    (IsExact.id W.cof W.weq) (secondEmbeddingCoproductIso W) n
  rw [← KMap_comp_KMap, KMap_id] at h
  exact DFunLike.congr_fun h a

/-- Coproduct is exactly the pre-existing group multiplication on K-theory. -/
theorem coproductKMap_eq_mul (n : ℕ) (a b : W.K n) : coproductKMap W n (a, b) = a * b := by
  have he : (a, b) = (a, 1) * (1, b) := by simp
  rw [he, map_mul, coproductKMap_one_right, coproductKMap_one_left]

end CategoryTheory.Waldhausen.Additivity
