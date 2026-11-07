/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.DVRDegreeOne

/-!
Consumers of the actual native K₁-to-K₀ norm–residue square.
The ring and fraction-field universes remain independent. No prime or tame hypothesis is used.
-/

noncomputable section

universe u v

open Stacks.Chow

example (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (x : MilnorKTheory L 1) :
    (milnorKTheoryOneAddEquiv K (milnorKNorm K L 1 x)).toMul =
      Units.map (Algebra.norm K : L →* K)
        (milnorKTheoryOneAddEquiv L x).toMul :=
  milnorKTheoryOneAddEquiv_milnorKNorm K L x

example (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (x : MilnorKTheory L 0) :
    milnorKTheoryZeroAddEquiv K (milnorKNorm K L 0 x) =
      (Module.finrank K L : ℤ) * milnorKTheoryZeroAddEquiv L x :=
  milnorKTheoryZeroAddEquiv_milnorKNorm K L x

variable (R S : Type u) (F E : Type v)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [IsLocalHom (algebraMap R S)]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
  [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [FiniteDimensional F E]

example (x : MilnorKTheory E 1) :
    dvrMilnorTameSymbol' R F 0 (milnorKNorm F E 1 x) =
      milnorKNorm (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) 0
        (dvrMilnorTameSymbol' S E 0 x) :=
  dvrMilnorTameSymbol'_milnorKNorm_one R S F E x

example :
    (dvrMilnorTameSymbol' R F 0).comp (milnorKNorm F E 1) =
      (milnorKNorm (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) 0).comp
        (dvrMilnorTameSymbol' S E 0) :=
  dvrMilnorTameSymbol'_comp_milnorKNorm_one R S F E

end
