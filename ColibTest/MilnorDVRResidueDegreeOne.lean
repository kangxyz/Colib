/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.DVRResidueDegreeOne

/-! Consumers of the true branch weights and lower residue-degree-one square. -/

noncomputable section

open IsLocalRing Module Stacks.Chow Stacks.DiscreteValuationRing.Ramification
open scoped BigOperators TensorProduct

universe u v w

variable (R S T : Type u)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [IsLocalHom (algebraMap R S)]
  [Algebra R T] [FaithfulSMul R T] [IsLocalHom (algebraMap R T)]
  (F E K : Type v)
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra R E] [Algebra S E] [IsFractionRing S E]
  [Algebra F E] [IsScalarTower R F E] [IsScalarTower R S E]
  [FiniteDimensional F E]
  [Field K] [Algebra T K] [IsFractionRing T K] [Algebra F K]
  {ι : Type w} [Fintype ι] (U : ι → Type u) (D : ι → Type v)
  [∀ i, CommRing (U i)] [∀ i, IsDomain (U i)] [∀ i, IsDiscreteValuationRing (U i)]
  [∀ i, Algebra R (U i)] [∀ i, Algebra S (U i)] [∀ i, Algebra T (U i)]
  [∀ i, IsScalarTower R S (U i)] [∀ i, IsScalarTower R T (U i)]
  [∀ i, FaithfulSMul S (U i)] [∀ i, Module.IsTorsionFree T (U i)]
  [∀ i, Module.Finite T (U i)]
  [∀ i, IsLocalHom (algebraMap S (U i))] [∀ i, IsLocalHom (algebraMap T (U i))]
  [∀ i, Field (D i)] [∀ i, Algebra (U i) (D i)] [∀ i, IsFractionRing (U i) (D i)]
  [∀ i, Algebra T (D i)] [∀ i, Algebra K (D i)]
  [∀ i, IsScalarTower T (U i) (D i)] [∀ i, IsScalarTower T K (D i)]
  [∀ i, FiniteDimensional K (D i)]

example
    (ε : K ⊗[F] E ≃ₐ[K] ∀ i, D i)
    (hf : finrank (ResidueField R) (ResidueField S) = 1)
    (y : MilnorKRing (ResidueField S)) :
    (∑ i, (Stacks.DiscreteValuationRing.Ramification.ramificationIdx S (U i) : ℤ) •
      milnorKNormRing (ResidueField T) (ResidueField (U i))
        (milnorKRingMap (algebraMap (ResidueField S) (ResidueField (U i))) y)) =
      (Stacks.DiscreteValuationRing.Ramification.ramificationIdx R T : ℤ) •
        milnorKRingMap (algebraMap (ResidueField R) (ResidueField T))
          (milnorKNormRing (ResidueField R) (ResidueField S) y) :=
  sum_ramification_smul_residue_norm_map_of_residue_finrank_eq_one R S T F E K U D ε hf y

example
    (ε : K ⊗[F] E ≃ₐ[K] ∀ i, D i)
    (hf : finrank (ResidueField R) (ResidueField S) = 1)
    (n : ℕ) (y : MilnorKTheory (ResidueField S) n) :
    (∑ i, (Stacks.DiscreteValuationRing.Ramification.ramificationIdx S (U i) : ℤ) •
      milnorKNorm (ResidueField T) (ResidueField (U i)) n
        (milnorKTheoryMap (algebraMap (ResidueField S) (ResidueField (U i))) n y)) =
      (Stacks.DiscreteValuationRing.Ramification.ramificationIdx R T : ℤ) •
        milnorKTheoryMap (algebraMap (ResidueField R) (ResidueField T)) n
          (milnorKNorm (ResidueField R) (ResidueField S) n y) :=
  sum_ramification_smul_residue_norm_map_of_residue_finrank_eq_one_homogeneous
    R S T F E K U D ε hf n y

end
