/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.Charpoly.IntegralTensorProduct

/-! Regression test for the literal integral-closure tensor product identity. -/

noncomputable section

open scoped TensorProduct

namespace ColibTest.IntegralTensorCharpolyProduct

theorem actual_integral_models
    (R F S E T L : Type*)
    [CommRing R] [IsDomain R] [Field F] [CommRing S] [Field E]
    [Algebra R F] [IsFractionRing R F] [Algebra R S] [Algebra F E]
    [Algebra R E] [Algebra S E] [IsScalarTower R F E] [IsScalarTower R S E]
    [IsIntegralClosure S R E] [FiniteDimensional F E]
    [Module.Free R S] [Module.Finite R S]
    [CommRing T] [IsDomain T] [Field L] [Algebra R T] [Algebra T L]
    [IsFractionRing T L] [Algebra F L] [Algebra R L]
    [IsScalarTower R T L] [IsScalarTower R F L]
    {ι : Type*} [Fintype ι] (D U : ι → Type*)
    [∀ i, Field (D i)] [∀ i, CommRing (U i)]
    [∀ i, Algebra L (D i)] [∀ i, Algebra T (U i)]
    [∀ i, Algebra T (D i)] [∀ i, Algebra (U i) (D i)]
    [∀ i, IsScalarTower T L (D i)] [∀ i, IsScalarTower T (U i) (D i)]
    [∀ i, IsIntegralClosure (U i) T (D i)] [∀ i, FiniteDimensional L (D i)]
    [∀ i, Module.Free T (U i)] [∀ i, Module.Finite T (U i)]
    (ε : (L ⊗[F] E) ≃ₐ[L] (∀ i, D i)) (b : S) (c : ∀ i, U i)
    (hc : ∀ i, algebraMap (U i) (D i) (c i) =
      ε (1 ⊗ₜ[F] (algebraMap S E b)) i) :
    ((Algebra.lmul R S b).charpoly).map (algebraMap R T) =
      ∏ i, (Algebra.lmul T (U i) (c i)).charpoly :=
  Algebra.map_charpoly_lmul_eq_prod_integralClosure R F S E T L D U ε b c hc

end ColibTest.IntegralTensorCharpolyProduct
