/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Residue.RamifiedMap

/-! Tests retain four independent universes and a genuine ramification unit. The degree-two
case tests the factor two, not vanishing in a residue field of characteristic two. -/

noncomputable section

universe u v w z

open Stacks.Chow

variable {R : Type u} {S : Type v}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  {F : Type w} {E : Type z} [Field F] [Field E]
  [Algebra R F] [IsFractionRing R F] [Algebra S E] [IsFractionRing S E]
  (j : R →+* S) [IsLocalHom j] (f : F →+* E)
  (hf : ∀ r : R, f (algebraMap R F r) = algebraMap S E (j r))
  {π : R} {ρ : S} (hπ : Irreducible π) (hρ : Irreducible ρ)

example (u : Sˣ) (e : ℕ) (hπmap : j π = (u : S) * ρ ^ e)
    (n : ℕ) (x : MilnorKTheory F (n + 1)) :
    dvrMilnorTameSymbol hρ n (milnorKTheoryMap f (n + 1) x) =
      (e : ℤ) • milnorKTheoryMap (IsLocalRing.ResidueField.map j) n
        (dvrMilnorTameSymbol hπ n x) :=
  DFunLike.congr_fun (dvrMilnorTameSymbol_map_ramified j f hf hπ hρ u e hπmap n) x

example (u : Sˣ) (hπmap : j π = (u : S) * ρ ^ 2) (x : MilnorKTheory F 2) :
    dvrMilnorTameSymbol hρ 1 (milnorKTheoryMap f 2 x) =
      (2 : ℤ) • milnorKTheoryMap (IsLocalRing.ResidueField.map j) 1
        (dvrMilnorTameSymbol hπ 1 x) :=
  DFunLike.congr_fun (dvrMilnorTameSymbol_map_ramified j f hf hπ hρ u 2 hπmap 1) x

example (n : ℕ) :
    (dvrMilnorTameSymbol (F := F) hπ n).comp
        (milnorKTheoryMap (RingHom.id F) (n + 1)).toAddMonoidHom =
      ((milnorKTheoryMap (IsLocalRing.ResidueField.map (RingHom.id R)) n).toAddMonoidHom.comp
        (dvrMilnorTameSymbol (F := F) hπ n)) := by
  simpa using dvrMilnorTameSymbol_map_ramified (RingHom.id R) (RingHom.id F)
    (fun _ => rfl) hπ hπ (1 : Rˣ) 1 (by simp) n

-- A negative source order retains the inverse of the ramification unit residue.
example (u : Sˣ) (e : ℕ) (hπmap : j π = (u : S) * ρ ^ e)
    (x : Fˣ) (hx : dvrFracOrd hπ x = -1) :
    dvrFracUnitPart hρ (Units.map f.toMonoidHom x) =
      Units.map (IsLocalRing.ResidueField.map j).toMonoidHom (dvrFracUnitPart hπ x) *
        (Units.map (IsLocalRing.residue S).toMonoidHom u)⁻¹ := by
  simpa only [hx, zpow_neg_one] using
    dvrFracUnitPart_map_ramified j f hf hπ hρ u e hπmap x

-- The main component retains the literal unit correction, rather than just its residue part.
example (u : Sˣ) (e : ℕ) (hπmap : j π = (u : S) * ρ ^ e) (l : List Fˣ) :
    MilnorKShift.main (dvrMilnorShiftMap hρ
        (milnorKSymbolProd E (l.map (Units.map f.toMonoidHom)))) =
      milnorKRingMapLift (IsLocalRing.ResidueField.map j)
          (MilnorKShift.main (dvrMilnorShiftMap hπ (milnorKSymbolProd F l))) +
        milnorKRingMapLift (IsLocalRing.ResidueField.map j)
          (MilnorKShift.shift (dvrMilnorShiftMap hπ (milnorKSymbolProd F l))) *
            milnorKSymbol (IsLocalRing.ResidueField S)
              (Units.map (IsLocalRing.residue S).toMonoidHom u) :=
  (dvrMilnorShiftMap_symbolProd_map_ramified j f hf hπ hρ u e hπmap l).1
