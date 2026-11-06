/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.MilnorK.Norm.DVRMixedCore

/-! Uncompiled native shift consumers, including even ramification and negative order. -/

noncomputable section

open Stacks.Chow

universe u v

example {k : Type u} [Field k] (M B A U : MilnorKRing k) (e d r : ℤ) :
    (d * r) • M - B * (e • A + r • ((d * (e - 1)) • milnorKNegOne k - U)) +
        (d * r) • (B * milnorKNegOne k) =
      (d * r) • M - e • (B * A) + r • (B * U) +
        (e * r * d) • (B * milnorKNegOne k) :=
  milnorK_norm_ramified_mixed_algebra M B A U e d r

example {k : Type u} [Field k] (M B A U : MilnorKRing k) :
    ((3 : ℤ) * (-1)) • M -
        B * ((2 : ℤ) • A + (-1 : ℤ) • (((3 : ℤ) * (2 - 1)) • milnorKNegOne k - U)) +
        ((3 : ℤ) * (-1)) • (B * milnorKNegOne k) =
      ((3 : ℤ) * (-1)) • M - (2 : ℤ) • (B * A) + (-1 : ℤ) • (B * U) +
        ((2 : ℤ) * (-1) * 3) • (B * milnorKNegOne k) :=
  milnorK_norm_ramified_mixed_algebra M B A U 2 3 (-1)

variable {R S : Type u}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  {F E : Type v} [Field F] [Field E]
  [Algebra R F] [IsFractionRing R F] [Algebra S E] [IsFractionRing S E]
  {π : R} {ϖ : S}

example (hπ : Irreducible π) (z : MilnorKRing F) (b : Fˣ) :
    MilnorKShift.shift (dvrMilnorShiftMap hπ (z * milnorKSymbol F b)) =
      dvrFracOrd hπ b • MilnorKShift.main (dvrMilnorShiftMap hπ z) -
        MilnorKShift.shift (dvrMilnorShiftMap hπ z) *
          milnorKSymbol (IsLocalRing.ResidueField R) (dvrFracUnitPart hπ b) +
        dvrFracOrd hπ b • (MilnorKShift.shift (dvrMilnorShiftMap hπ z) *
          milnorKNegOne (IsLocalRing.ResidueField R)) :=
  dvrMilnorShiftMap_shift_mul_symbol hπ z b

example (j : R →+* S) [IsLocalHom j] (f : F →+* E)
    (hf : ∀ a : R, f (algebraMap R F a) = algebraMap S E (j a))
    (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : j π = (u : S) * ϖ ^ e) (z : MilnorKRing F) :
    MilnorKShift.shift (dvrMilnorShiftMap hϖ (milnorKRingMap f z)) =
      (e : ℤ) • milnorKRingMap (IsLocalRing.ResidueField.map j)
        (MilnorKShift.shift (dvrMilnorShiftMap hπ z)) :=
  (dvrMilnorShiftMap_map_ramified j f hf hπ hϖ u e he z).2

end
