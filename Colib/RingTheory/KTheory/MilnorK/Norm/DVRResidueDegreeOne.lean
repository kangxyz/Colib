/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Symbols.Transport
public import Colib.RingTheory.DiscreteValuationRing.BranchDegree
public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.FieldNorm

/-!
# The weighted residue norm square in residue degree one

For an actual square of DVR maps with a full generic tensor decomposition, the lower
weighted residue square follows from the native degree projection when the original
residue extension has degree one. The local fundamental identity, the native ideal
ramification tower identity and the rank of the entire tensor product supply the total
weight. No branch is discarded and no ramification integer is cancelled in a Milnor group.

No normality, prime degree, characteristic, separability, Henselianity, power basis or norm
tower law is used. This establishes one case of the lower branch square, not a construction
of the branches or the full norm-residue compatibility theorem. The tensor equivalence is
used only for its total degree identity; compatibility of its individual field coordinates
with the integral maps must still be established by the actual branch construction.
-/

@[expose] public noncomputable section

open IsLocalRing Module
open scoped BigOperators TensorProduct

universe u v w

namespace Stacks.Chow

open DiscreteValuationRing.Ramification

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

/-- The lower weighted residue norm square in residue degree one, for the actual integral
square and all factors of the full generic tensor decomposition. -/
theorem sum_ramification_smul_residue_norm_map_of_residue_finrank_eq_one
    (ε : K ⊗[F] E ≃ₐ[K] ∀ i, D i)
    (hf : finrank (ResidueField R) (ResidueField S) = 1)
    (y : MilnorKRing (ResidueField S)) :
    (∑ i, (DiscreteValuationRing.Ramification.ramificationIdx S (U i) : ℤ) •
      milnorKNormRing (ResidueField T) (ResidueField (U i))
        (milnorKRingMap (algebraMap (ResidueField S) (ResidueField (U i))) y)) =
      (DiscreteValuationRing.Ramification.ramificationIdx R T : ℤ) •
        milnorKRingMap (algebraMap (ResidueField R) (ResidueField T))
          (milnorKNormRing (ResidueField R) (ResidueField S) y) := by
  classical
  let : ∀ i, IsLocalHom (algebraMap R (U i)) := fun i => by
    rw [IsScalarTower.algebraMap_eq R S (U i)]
    infer_instance
  have hb : Function.Bijective (algebraMap (ResidueField R) (ResidueField S)) :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hf
  let z := milnorKNormRing (ResidueField R) (ResidueField S) y
  have hy : milnorKRingMap (algebraMap (ResidueField R) (ResidueField S)) z = y := by
    dsimp only [z]
    rw [milnorKNormRing_of_bijective hb]
    let g := RingEquiv.ofBijective (algebraMap (ResidueField R) (ResidueField S)) hb
    change milnorKRingMap (g : ResidueField R →+* ResidueField S)
      (milnorKRingMap (g.symm : ResidueField S →+* ResidueField R) y) = y
    rw [milnorKRingMap_comp_apply, RingEquiv.comp_symm, milnorKRingMap_id_apply]
  have hnorm (i : ι) :
      milnorKNormRing (ResidueField T) (ResidueField (U i))
        (milnorKRingMap (algebraMap (ResidueField S) (ResidueField (U i))) y) =
      (finrank (ResidueField T) (ResidueField (U i)) : ℤ) •
        milnorKRingMap (algebraMap (ResidueField R) (ResidueField T)) z := by
    rw [← hy, milnorKRingMap_comp_apply, ← IsScalarTower.algebraMap_eq,
      IsScalarTower.algebraMap_eq (ResidueField R) (ResidueField T) (ResidueField (U i)),
      ← milnorKRingMap_comp_apply, milnorKNormRing_milnorKRingMap]
  simp_rw [hnorm, smul_smul, ← Nat.cast_mul]
  rw [← Finset.sum_smul, ← Nat.cast_sum,
    sum_ramification_mul_residue_finrank_of_residue_finrank_eq_one
      R S T F E K U D ε hf]

/-- Homogeneous lower weighted residue compatibility, including degree zero. -/
theorem sum_ramification_smul_residue_norm_map_of_residue_finrank_eq_one_homogeneous
    (ε : K ⊗[F] E ≃ₐ[K] ∀ i, D i)
    (hf : finrank (ResidueField R) (ResidueField S) = 1)
    (n : ℕ) (y : MilnorKTheory (ResidueField S) n) :
    (∑ i, (DiscreteValuationRing.Ramification.ramificationIdx S (U i) : ℤ) •
      milnorKNorm (ResidueField T) (ResidueField (U i)) n
        (milnorKTheoryMap (algebraMap (ResidueField S) (ResidueField (U i))) n y)) =
      (DiscreteValuationRing.Ramification.ramificationIdx R T : ℤ) •
        milnorKTheoryMap (algebraMap (ResidueField R) (ResidueField T)) n
          (milnorKNorm (ResidueField R) (ResidueField S) n y) := by
  classical
  apply Subtype.ext
  change (milnorKGrading (ResidueField T) n).subtype
      (∑ i, (DiscreteValuationRing.Ramification.ramificationIdx S (U i) : ℤ) •
        milnorKNorm (ResidueField T) (ResidueField (U i)) n
          (milnorKTheoryMap (algebraMap (ResidueField S) (ResidueField (U i))) n y)) =
    (milnorKGrading (ResidueField T) n).subtype
      ((DiscreteValuationRing.Ramification.ramificationIdx R T : ℤ) •
        milnorKTheoryMap (algebraMap (ResidueField R) (ResidueField T)) n
          (milnorKNorm (ResidueField R) (ResidueField S) n y))
  rw [map_sum]
  simp_rw [map_zsmul, milnorKTheoryMap_eq_transport]
  exact sum_ramification_smul_residue_norm_map_of_residue_finrank_eq_one
    R S T F E K U D ε hf (y : MilnorKRing (ResidueField S))

end Stacks.Chow

end
