/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.DVRMixedCharZero

noncomputable section

open IsLocalRing Stacks.Chow

universe u v

variable (R S : Type u) (F E : Type v)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [IsLocalHom (algebraMap R S)]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
  [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [FiniteDimensional F E]


example (hdegree : Module.finrank F E = 1) (m : ℕ)
    (x : MilnorKTheory E (m + 1))
    (hx : x ∈ milnorKMixedSpan (algebraMap F E) m) :
    dvrMilnorTameSymbol' R F m (milnorKNorm F E (m + 1) x) =
      milnorKNorm (ResidueField R) (ResidueField S) m (dvrMilnorTameSymbol' S E m x) :=
  dvrMilnorTameSymbol'_milnorKNorm_of_mem_mixedSpan_of_finrank_eq_one
    R S F E hdegree m x hx

example [HenselianLocalRing S] [CharZero (ResidueField R)]
    (hprime : Nat.Prime (Module.finrank F E)) (m : ℕ)
    (x : MilnorKTheory E (m + 1))
    (hx : x ∈ milnorKMixedSpan (algebraMap F E) m) :
    dvrMilnorTameSymbol' R F m (milnorKNorm F E (m + 1) x) =
      milnorKNorm (ResidueField R) (ResidueField S) m (dvrMilnorTameSymbol' S E m x) :=
  dvrMilnorTameSymbol'_milnorKNorm_of_mem_mixedSpan_of_prime_degree_of_charZero
    R S F E hprime m x hx

example [HenselianLocalRing S] [CharZero (ResidueField R)]
    (hdegree : Module.finrank F E = 1 ∨ Nat.Prime (Module.finrank F E)) (m : ℕ)
    (x : MilnorKTheory E (m + 1))
    (hx : x ∈ milnorKMixedSpan (algebraMap F E) m) :
    dvrMilnorTameSymbol' R F m (milnorKNorm F E (m + 1) x) =
      milnorKNorm (ResidueField R) (ResidueField S) m (dvrMilnorTameSymbol' S E m x) :=
  dvrMilnorTameSymbol'_milnorKNorm_of_mem_mixedSpan_of_one_or_prime_of_charZero
    R S F E hdegree m x hx

example [HenselianLocalRing S] [CharZero (ResidueField R)]
    (hdegree : Module.finrank F E = 1 ∨ Nat.Prime (Module.finrank F E))
    (x : MilnorKTheory E 1)
    (hx : x ∈ milnorKMixedSpan (algebraMap F E) 0) :
    dvrMilnorTameSymbol' R F 0 (milnorKNorm F E 1 x) =
      milnorKNorm (ResidueField R) (ResidueField S) 0 (dvrMilnorTameSymbol' S E 0 x) :=
  dvrMilnorTameSymbol'_milnorKNorm_of_mem_mixedSpan_of_one_or_prime_of_charZero
    R S F E hdegree 0 x hx

end
