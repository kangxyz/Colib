/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.MilnorK.Residue.UnramifiedMapAcross

/-!
# Common-universe compatibility for unramified tame residue maps

The old same-DVR-universe interfaces are wrappers around the four-universe proofs.
Only specified uniformizers and ramification index one are covered. Canonical
arbitrary-uniformizer naturality and other ramification indices remain separate.
-/

@[expose] public noncomputable section

universe u v w

namespace Stacks.Chow

variable {R S : Type u}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  {F : Type v} {E : Type w} [Field F] [Field E]
  [Algebra R F] [IsFractionRing R F] [Algebra S E] [IsFractionRing S E]
  (j : R →+* S) [IsLocalHom j] (f : F →+* E)
  (hf : ∀ r : R, f (algebraMap R F r) = algebraMap S E (j r))
  {π : R}

include hf

omit [IsLocalHom j] in
/-- Compatibility specialization of the four-universe native theorem. -/
theorem dvrFracOrd_map (hπ : Irreducible π) (hjπ : Irreducible (j π)) (x : Fˣ) :
    dvrFracOrd hjπ (Units.map f.toMonoidHom x) = dvrFracOrd hπ x :=
  dvrFracOrd_map_across j f hf hπ hjπ x

/-- Compatibility specialization of the four-universe native theorem. -/
theorem dvrMilnorShiftMap_shift_symbolProd_map (hπ : Irreducible π)
    (hjπ : Irreducible (j π)) (l : List Fˣ) :
    milnorKRingMap (IsLocalRing.ResidueField.map j)
        (MilnorKShift.shift (dvrMilnorShiftMap hπ (milnorKSymbolProd F l))) =
      MilnorKShift.shift (dvrMilnorShiftMap hjπ
        (milnorKSymbolProd E (l.map (Units.map f.toMonoidHom)))) := by
  simpa only [milnorKRingMapLift_eq] using
    dvrMilnorShiftMap_shift_symbolProd_map_across j f hf hπ hjπ l

/-- Compatibility specialization of the four-universe native theorem. -/
theorem dvrMilnorTameSymbol_map (hπ : Irreducible π) (hjπ : Irreducible (j π)) (n : ℕ) :
    (milnorKTheoryMap (IsLocalRing.ResidueField.map j) n).toAddMonoidHom.comp
        (dvrMilnorTameSymbol (F := F) hπ n) =
      (dvrMilnorTameSymbol (F := E) hjπ n).comp (milnorKTheoryMap f (n + 1)).toAddMonoidHom :=
  dvrMilnorTameSymbol_map_across j f hf hπ hjπ n

end Stacks.Chow

attribute [colib_tag "COL-0131"]
  Stacks.Chow.dvrFracOrd_map
  Stacks.Chow.dvrMilnorShiftMap_shift_symbolProd_map
  Stacks.Chow.dvrMilnorTameSymbol_map

add_to_stacks 0EAY "DVR tame-symbol background; formula follows from native shift multiplication"
  Stacks.Chow.dvrMilnorTameSymbol_map
