/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.DVRAngularComponent

/-! Consumers of the actual norm angular component, retaining negative orders.-/

noncomputable section

open IsLocalRing Stacks.Chow

universe u v

example {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {F : Type v} [Field F] [Algebra R F] [IsFractionRing R F]
    {π : R} (hπ : Irreducible π) (x : Fˣ) :
    dvrFracUnitPart hπ (x ^ (-2 : ℤ)) = dvrFracUnitPart hπ x ^ (-2 : ℤ) :=
  dvrFracUnitPart_zpow hπ x (-2)

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
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e) (a : Sˣ) :
    dvrFracUnitPart hπ
        (Units.map (Algebra.norm F) (Units.map (algebraMap S E).toMonoidHom a)) =
      Units.map (Algebra.norm (ResidueField R)) (Units.map (residue S).toMonoidHom a) ^ e :=
  dvrFracUnitPart_norm_unitsMap R S F E hπ hϖ u e he a

example (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (b₀ : Rˣ) (hb₀ : Algebra.intNorm R S ϖ =
      π ^ Module.finrank (ResidueField R) (ResidueField S) * (b₀ : R)) (b : Eˣ) :
    dvrFracUnitPart hπ (Units.map (Algebra.norm F) b) =
      Units.map (Algebra.norm (ResidueField R)) (dvrFracUnitPart hϖ b) ^ e *
        (Units.map (residue R).toMonoidHom b₀) ^ dvrFracOrd hϖ b :=
  dvrFracUnitPart_norm_of_coefficient R S F E hπ hϖ u e he b₀ hb₀ b

example (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (he : algebraMap R S π = (u : S) * ϖ) (b : Eˣ) :
    dvrFracUnitPart hπ (Units.map (Algebra.norm F) b) =
      Units.map (Algebra.norm (ResidueField R)) (dvrFracUnitPart hϖ b) *
        (Units.map (Algebra.norm (ResidueField R))
          (Units.map (residue S).toMonoidHom u))⁻¹ ^ dvrFracOrd hϖ b :=
  dvrFracUnitPart_norm_of_exponent_one R S F E hπ hϖ u he b

example [HenselianLocalRing S] (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)
    (heunit : IsUnit (e : S)) (hp : Nat.Prime (Module.finrank F E)) (b : Eˣ) :
    dvrFracUnitPart hπ (Units.map (Algebra.norm F) b) =
      Units.map (Algebra.norm (ResidueField R)) (dvrFracUnitPart hϖ b) ^ e *
        (((-1 : (ResidueField R)ˣ) ^
            (Module.finrank (ResidueField R) (ResidueField S) * (e - 1))) *
          (Units.map (Algebra.norm (ResidueField R))
            (Units.map (residue S).toMonoidHom u))⁻¹) ^ dvrFracOrd hϖ b :=
  dvrFracUnitPart_norm_of_prime_degree R S F E hπ hϖ u e he heunit hp b

end
