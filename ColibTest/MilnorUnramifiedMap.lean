module

import Colib.RingTheory.KTheory.MilnorK.Residue.UnramifiedMap

open Stacks.Chow

universe u v w

variable {R S : Type u}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  {F : Type v} {E : Type w} [Field F] [Field E]
  [Algebra R F] [IsFractionRing R F] [Algebra S E] [IsFractionRing S E]
  (j : R →+* S) [IsLocalHom j] (f : F →+* E)
  (hf : ∀ r : R, f (algebraMap R F r) = algebraMap S E (j r))
  {π : R} (hπ : Irreducible π) (hjπ : Irreducible (j π))

-- Arbitrary classes and all residue degrees, with independent fraction-field universes.
example (n : ℕ) (x : MilnorKTheory F (n + 1)) :
    milnorKTheoryMap (IsLocalRing.ResidueField.map j) n (dvrMilnorTameSymbol hπ n x) =
      dvrMilnorTameSymbol hjπ n (milnorKTheoryMap f (n + 1) x) :=
  DFunLike.congr_fun (dvrMilnorTameSymbol_map j f hf hπ hjπ n) x

-- The degree-one residue lands in degree zero; no positivity assumption is hidden.
example (x : MilnorKTheory F 1) :
    milnorKTheoryMap (IsLocalRing.ResidueField.map j) 0 (dvrMilnorTameSymbol hπ 0 x) =
      dvrMilnorTameSymbol hjπ 0 (milnorKTheoryMap f 1 x) :=
  DFunLike.congr_fun (dvrMilnorTameSymbol_map j f hf hπ hjπ 0) x
