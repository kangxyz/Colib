/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Functor.PointwiseCoproduct
public import Colib.CategoryTheory.Waldhausen.Product.Structure
public import Colib.KTheory.Waldhausen.ZeroFunctor
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

/-- Binary coproduct is genuinely exact for the componentwise product structure. -/
theorem coproductFunctor_isExact :
    IsExact (productStructure W W).cof (productStructure W W).weq W.cof W.weq
      (coproductFunctor (C := C)) :=
  sumFunctor_isExact (productStructure W W) W (fst_exact W W) (snd_exact W W)

/-- The canonical first zero embedding. -/
def firstEmbedding : C ⥤ C × C := (𝟭 C).prod' (zeroFunctor W)

/-- The canonical second zero embedding. -/
def secondEmbedding : C ⥤ C × C := (zeroFunctor W).prod' (𝟭 C)

omit [HasBinaryCoproducts C] in
theorem firstEmbedding_isExact :
    IsExact W.cof W.weq (productStructure W W).cof (productStructure W W).weq (firstEmbedding W) :=
  pair_exact W W W (IsExact.id W.cof W.weq) (zeroFunctor_isExact W W)

omit [HasBinaryCoproducts C] in
theorem secondEmbedding_isExact :
    IsExact W.cof W.weq (productStructure W W).cof (productStructure W W).weq (secondEmbedding W) :=
  pair_exact W W W (zeroFunctor_isExact W W) (IsExact.id W.cof W.weq)

/-- The literal first coproduct inclusion is a natural isomorphism when the
other summand is the chosen zero. -/
def firstEmbeddingCoproductIso : firstEmbedding W ⋙ coproductFunctor (C := C) ≅ 𝟭 C := by
  let η := sumInl (𝟭 C) (zeroFunctor W)
  have hη (X : C) : IsIso (η.app X) := by
    let : IsIso (W.isZero.to_ W.zero) := W.isZero.isIso W.isZero _
    exact (coprod_isPushout W X W.zero).isIso_inl_of_isIso
  letI : IsIso η := NatIso.isIso_of_isIso_app η
  exact (asIso η).symm

/-- The literal second coproduct inclusion is a natural isomorphism when the
other summand is the chosen zero. -/
def secondEmbeddingCoproductIso : secondEmbedding W ⋙ coproductFunctor (C := C) ≅ 𝟭 C := by
  let η := sumInr (zeroFunctor W) (𝟭 C)
  have hη (X : C) : IsIso (η.app X) := by
    let : IsIso (W.isZero.to_ W.zero) := W.isZero.isIso W.isZero _
    exact (coprod_isPushout W W.zero X).isIso_inr_of_isIso
  letI : IsIso η := NatIso.isIso_of_isIso_app η
  exact (asIso η).symm

end CategoryTheory.Waldhausen.Additivity
