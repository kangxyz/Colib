/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.DVRPrimeAnnihilation

/-! Regression consumers of the weighted restriction and prime annihilator, not equality. -/

noncomputable section

open Stacks.Chow IsLocalRing Module

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

example (hp : Nat.Prime (finrank F E)) (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    (Stacks.DiscreteValuationRing.Ramification.ramificationIdx R S : ℤ) •
      milnorKTheoryMap (algebraMap (ResidueField R) (ResidueField S)) n
        (dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) -
          milnorKNorm (ResidueField R) (ResidueField S) n
            (dvrMilnorTameSymbol' S E n x)) = 0 :=
  ramification_smul_restrict_norm_residue_difference_eq_zero R S F E hp n x

example (hp : Nat.Prime (finrank F E)) (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    (finrank F E : ℤ) •
      (dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) -
        milnorKNorm (ResidueField R) (ResidueField S) n
          (dvrMilnorTameSymbol' S E n x)) = 0 :=
  finrank_smul_norm_residue_difference_eq_zero R S F E hp n x

example (hp : Nat.Prime (finrank F E)) (x : MilnorKTheory E 1) :
    (finrank F E : ℤ) •
      (dvrMilnorTameSymbol' R F 0 (milnorKNorm F E 1 x) -
        milnorKNorm (ResidueField R) (ResidueField S) 0
          (dvrMilnorTameSymbol' S E 0 x)) = 0 :=
  finrank_smul_norm_residue_difference_eq_zero R S F E hp 0 x

end
