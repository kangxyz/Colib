/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.DVRPrimeCharZero

/-!
# Consumers of the prime Galois characteristic-zero residue square

No Henselianity, auxiliary mixed witness, branch map, or torsion-free Milnor hypothesis is added.
-/

noncomputable section

open IsLocalRing Module Stacks.Chow

universe u

variable (R S F E : Type u)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [IsLocalHom (algebraMap R S)]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
  [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [FiniteDimensional F E] [IsGalois F E] [CharZero (ResidueField R)]

example (hp : Nat.Prime (finrank F E)) (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    ∃ d : ℕ, (finrank F E).Coprime d ∧
      (d : ℤ) •
        (dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) -
          milnorKNorm (ResidueField R) (ResidueField S) n
            (dvrMilnorTameSymbol' S E n x)) = 0 :=
  exists_coprime_smul_norm_residue_difference_eq_zero_of_charZero R S F E hp n x

example (hp : Nat.Prime (finrank F E)) (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) =
      milnorKNorm (ResidueField R) (ResidueField S) n (dvrMilnorTameSymbol' S E n x) :=
  dvrMilnorTameSymbol'_milnorKNorm_of_prime_galois_of_charZero R S F E hp n x

example (hp : Nat.Prime (finrank F E)) (x : MilnorKTheory E 1) :
    dvrMilnorTameSymbol' R F 0 (milnorKNorm F E 1 x) =
      milnorKNorm (ResidueField R) (ResidueField S) 0 (dvrMilnorTameSymbol' S E 0 x) :=
  dvrMilnorTameSymbol'_milnorKNorm_of_prime_galois_of_charZero R S F E hp 0 x

example (hp : Nat.Prime (finrank F E)) (n : ℕ) :
    (dvrMilnorTameSymbol' R F n).comp (milnorKNorm F E (n + 1)) =
      (milnorKNorm (ResidueField R) (ResidueField S) n).comp
        (dvrMilnorTameSymbol' S E n) :=
  dvrMilnorTameSymbol'_comp_milnorKNorm_of_prime_galois_of_charZero R S F E hp n

end
