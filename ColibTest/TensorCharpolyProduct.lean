/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.Charpoly.TensorProduct

/-! Regression tests for the literal tensor decomposition characteristic polynomial. -/

noncomputable section

open scoped TensorProduct

namespace ColibTest.TensorCharpolyProduct

/-- Algebra equivalence transports the actual multiplication operator. -/
theorem actual_algebra_equivalence
    {k A B : Type*} [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B]
    [FiniteDimensional k A] [FiniteDimensional k B] (ε : A ≃ₐ[k] B) (a : A) :
    (Algebra.lmul k B (ε a)).charpoly = (Algebra.lmul k A a).charpoly :=
  Algebra.charpoly_lmul_algEquiv ε a

/-- Binary multiplication is the actual block-diagonal product operator. -/
theorem actual_binary_product
    {k A B : Type*} [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B]
    [FiniteDimensional k A] [FiniteDimensional k B] (a : A × B) :
    (Algebra.lmul k (A × B) a).charpoly =
      (Algebra.lmul k A a.1).charpoly * (Algebra.lmul k B a.2).charpoly :=
  Algebra.charpoly_lmul_prod a

/-- The finite-product theorem includes the empty product algebra. -/
theorem empty_product (k : Type*) [Field k] :
    (Algebra.lmul k (PEmpty → k) (fun i ↦ PEmpty.elim i)).charpoly = 1 := by
  simpa using Algebra.charpoly_lmul_pi (k := k) (fun _ : PEmpty ↦ k)
    (fun i ↦ PEmpty.elim i)

variable {F E L : Type*} [Field F] [Field E] [Field L]
  [Algebra F E] [Algebra F L] [FiniteDimensional F E]
  {ι : Type*} [Fintype ι] (D : ι → Type*) [∀ i, Field (D i)]
  [∀ i, Algebra L (D i)] [∀ i, FiniteDimensional L (D i)]

/-- The product uses the actual tensor images, without assumed factor identities. -/
theorem literal_tensor_images (ε : (L ⊗[F] E) ≃ₐ[L] (∀ i, D i)) (b : E) :
    ((Algebra.lmul F E b).charpoly).map (algebraMap F L) =
      ∏ i, (Algebra.lmul L (D i) ((ε (1 ⊗ₜ[F] b)) i)).charpoly :=
  Algebra.map_charpoly_lmul_eq_prod_tensor D ε b

/-- The dependent finite-product formula is itself proved, not an input. -/
theorem actual_product (a : ∀ i, D i) :
    (Algebra.lmul L (∀ i, D i) a).charpoly =
      ∏ i, (Algebra.lmul L (D i) (a i)).charpoly :=
  Algebra.charpoly_lmul_pi D a

end ColibTest.TensorCharpolyProduct
