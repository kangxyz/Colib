module

import Colib.KTheory.MilnorK.Residue.Naturality

open Stacks.Chow

universe u v w z

variable {R : Type u} {S : Type v}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  {F : Type w} {E : Type z} [Field F] [Field E]
  [Algebra R F] [IsFractionRing R F] [Algebra S E] [IsFractionRing S E]
  (j : R →+* S) [IsLocalHom j] (f : F →+* E)
  (hf : ∀ r : R, f (algebraMap R F r) = algebraMap S E (j r))
  {π : R} (hπ : Irreducible π) (hjπ : Irreducible (j π))

-- Arbitrary classes, rather than only symbols, and four independent universes.
example (n : ℕ) (x : MilnorKTheory F n) :
    milnorKTheoryMap (IsLocalRing.ResidueField.map j) n
        (dvrMilnorSpecialization hπ n x) =
      dvrMilnorSpecialization hjπ n (milnorKTheoryMap f n x) :=
  LinearMap.congr_fun (dvrMilnorSpecialization_map j f hf hπ hjπ n) x

-- Degree zero is included without positivity hypotheses.
example (x : MilnorKTheory F 0) :
    milnorKTheoryMap (IsLocalRing.ResidueField.map j) 0
        (dvrMilnorSpecialization hπ 0 x) =
      dvrMilnorSpecialization hjπ 0 (milnorKTheoryMap f 0 x) :=
  LinearMap.congr_fun (dvrMilnorSpecialization_map j f hf hπ hjπ 0) x
