/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.MilnorK.Norm.DVRMixed
import Colib.KTheory.MilnorK.Norm.DVRDegreeOne

/-!
Uncompiled consumers of the canonical native square on the existing mixed span.
The coefficient premise, exponent-one case, and Henselian/tame prime case stay distinct.
The degree-one regression explicitly uses the already compiled unconditional theorem.
-/

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
  [FiniteDimensional F E] {π : R} {ϖ : S}

example (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (b₀ : Rˣ) (hb₀ : Algebra.intNorm R S ϖ =
      π ^ Module.finrank (ResidueField R) (ResidueField S) * (b₀ : R))
    (hres : residue R (b₀ : R) =
      (-1 : ResidueField R) ^ (Module.finrank (ResidueField R) (ResidueField S) * (e - 1)) *
        (Algebra.norm (ResidueField R) (residue S (u : S)))⁻¹)
    (z : MilnorKRing F) (b : Eˣ) :
    MilnorKShift.shift (dvrMilnorShiftMap hπ (milnorKNormRing F E
        (milnorKRingMap (algebraMap F E) z * milnorKSymbol E b))) =
      milnorKNormRing (ResidueField R) (ResidueField S)
        (MilnorKShift.shift (dvrMilnorShiftMap hϖ
          (milnorKRingMap (algebraMap F E) z * milnorKSymbol E b))) :=
  dvrMilnorShiftMap_shift_norm_mixed_of_exact_coefficient
    R S F E hπ hϖ u e he b₀ hb₀ hres z b

example (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (b₀ : Rˣ) (hb₀ : Algebra.intNorm R S ϖ =
      π ^ Module.finrank (ResidueField R) (ResidueField S) * (b₀ : R))
    (hres : residue R (b₀ : R) =
      (-1 : ResidueField R) ^ (Module.finrank (ResidueField R) (ResidueField S) * (e - 1)) *
        (Algebra.norm (ResidueField R) (residue S (u : S)))⁻¹)
    (m : ℕ) (x : MilnorKTheory E (m + 1))
    (hx : x ∈ milnorKMixedSpan (algebraMap F E) m) :
    dvrMilnorTameSymbol' R F m (milnorKNorm F E (m + 1) x) =
      milnorKNorm (ResidueField R) (ResidueField S) m (dvrMilnorTameSymbol' S E m x) :=
  dvrMilnorTameSymbol'_milnorKNorm_of_mem_mixedSpan_of_exact_coefficient
    R S F E hπ hϖ u e he b₀ hb₀ hres m x hx

example (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (he : algebraMap R S π = (u : S) * ϖ)
    (m : ℕ) (x : MilnorKTheory E (m + 1))
    (hx : x ∈ milnorKMixedSpan (algebraMap F E) m) :
    dvrMilnorTameSymbol' R F m (milnorKNorm F E (m + 1) x) =
      milnorKNorm (ResidueField R) (ResidueField S) m (dvrMilnorTameSymbol' S E m x) :=
  dvrMilnorTameSymbol'_milnorKNorm_of_mem_mixedSpan_of_exponent_one
    R S F E hπ hϖ u he m x hx

example [HenselianLocalRing S] (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (heunit : IsUnit (e : S)) (hp : Nat.Prime (Module.finrank F E))
    (m : ℕ) (x : MilnorKTheory E (m + 1))
    (hx : x ∈ milnorKMixedSpan (algebraMap F E) m) :
    dvrMilnorTameSymbol' R F m (milnorKNorm F E (m + 1) x) =
      milnorKNorm (ResidueField R) (ResidueField S) m (dvrMilnorTameSymbol' S E m x) :=
  dvrMilnorTameSymbol'_milnorKNorm_of_mem_mixedSpan_of_prime_degree
    R S F E hπ hϖ u e he heunit hp m x hx

example (x : MilnorKTheory E 1) :
    dvrMilnorTameSymbol' R F 0 (milnorKNorm F E 1 x) =
      milnorKNorm (ResidueField R) (ResidueField S) 0 (dvrMilnorTameSymbol' S E 0 x) :=
  dvrMilnorTameSymbol'_milnorKNorm_one R S F E x

example [HenselianLocalRing S] (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (heunit : IsUnit (e : S)) (hp : Nat.Prime (Module.finrank F E))
    (m : ℕ) (a : Fin m → Fˣ) (b : Eˣ) :
    let x := milnorKTupleSymbol (Fin.snoc (Units.map (algebraMap F E).toMonoidHom ∘ a) b)
    dvrMilnorTameSymbol' R F m (milnorKNorm F E (m + 1) x) =
      milnorKNorm (ResidueField R) (ResidueField S) m (dvrMilnorTameSymbol' S E m x) :=
  dvrMilnorTameSymbol'_milnorKNorm_of_mem_mixedSpan_of_prime_degree
    R S F E hπ hϖ u e he heunit hp m _
      (milnorKTupleSymbol_snoc_mem_mixedSpan (algebraMap F E) m a b)

end
