/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.Product.KEquivalence
public import Colib.KTheory.Waldhausen.Functoriality

/-! # Original K-maps into an actual product category -/
/-! Source: `Quillen/Waldhausen/Product/Functoriality.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual maps and universes are retained.
The S-product isomorphism is not a normalized or strict S-model comparison. -/
@[expose] public section

open CategoryTheory.Waldhausen.Product

noncomputable section
open CategoryTheory
universe u v

namespace CategoryTheory.Waldhausen.Product
open CategoryTheory.Waldhausen.Product
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
variable (U : Structure C) (V : Structure D) (W : Structure E)
variable {F : C ⥤ D} {G : C ⥤ E}

/-- Actual pairing of exact functors gives the pair of the original K-maps. -/
theorem KEquiv_pair_apply
    (hF : IsExact U.cof U.weq V.cof V.weq F)
    (hG : IsExact U.cof U.weq W.cof W.weq G) (n : ℕ) (a : U.K n) :
    KEquiv V W n (KMap (pair_exact U V W hF hG) n a) =
      (KMap hF n a, KMap hG n a) := by
  apply _root_.Prod.ext
  · exact (DFunLike.congr_fun
      (KMap_comp_KMap (pair_exact U V W hF hG) (fst_exact V W) n).symm a).symm
  · exact (DFunLike.congr_fun
      (KMap_comp_KMap (pair_exact U V W hF hG) (snd_exact V W) n).symm a).symm

end CategoryTheory.Waldhausen.Product
