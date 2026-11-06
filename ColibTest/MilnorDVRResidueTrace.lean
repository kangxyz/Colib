/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.MilnorK.Norm.DVRResidueTrace

/-!
Regression consumers of the actual finite local DVR residue trace.
The original generic Galois group remains the index set. No residue
separability, residue perfectness, trace identity, or norm tower is assumed.
-/

noncomputable section

open IsLocalRing Module Stacks.Chow
open scoped BigOperators

universe u v

variable (R S : Type u) (F E : Type v)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [IsLocalHom (algebraMap R S)]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
  [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [FiniteDimensional F E] [IsGalois F E]

example : Normal (ResidueField R) (ResidueField S) ∧
    Function.Surjective (fun σ : Gal(E/F) =>
      ResidueField.mapAlgEquiv' (galRestrict R F E S σ)) :=
  dvr_residueField_normal_and_galRestrict_surjective R S F E

example (hp : Nat.Prime (finrank F E)) (y : MilnorKRing (ResidueField S)) :
    (∑ σ : Gal(E/F),
      milnorKRingMap (ResidueField.map (galRestrict R F E S σ : S →+* S)) y) =
        (Stacks.DiscreteValuationRing.Ramification.ramificationIdx R S : ℤ) •
          milnorKRingMap (algebraMap (ResidueField R) (ResidueField S))
            (milnorKNormRing (ResidueField R) (ResidueField S) y) :=
  dvr_sum_residue_galRestrict_eq_ramification_smul_norm R S F E hp y

example (hp : Nat.Prime (finrank F E)) (n : ℕ) (y : MilnorKTheory (ResidueField S) n) :
    (∑ σ : Gal(E/F),
      milnorKTheoryMap (ResidueField.map (galRestrict R F E S σ : S →+* S)) n y) =
        (Stacks.DiscreteValuationRing.Ramification.ramificationIdx R S : ℤ) •
          milnorKTheoryMap (algebraMap (ResidueField R) (ResidueField S)) n
            (milnorKNorm (ResidueField R) (ResidueField S) n y) :=
  dvr_sum_residue_galRestrict_eq_ramification_smul_norm_homogeneous R S F E hp n y

end
