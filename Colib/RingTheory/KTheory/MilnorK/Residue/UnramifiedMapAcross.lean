/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Residue.Naturality
public import Colib.RingTheory.KTheory.MilnorK.Symbols.RingTransport
public import Colib.RingTheory.KTheory.MilnorK.Symbols.Involution

/-!
# Four-universe unramified residue naturality

This extends the specified-uniformizer e=1 naturality square to independent universes for both
DVRs and both fraction fields. The ring-level transport is the universal extension of the native
map, checked against the original map in a common universe and against `milnorKTheoryMap` in
each homogeneous degree. No residue, grading, quotient, or involution model is reconstructed.

Source: `MilnorK.DVR.residue_restrict` in `Aglib.KTheory.MilnorK.Residue.Restriction`, revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`. The specified-uniformizer formulation is retained;
canonical arbitrary-uniformizer naturality and ramification indices other than one are not claimed.
-/

@[expose] public noncomputable section

universe u v w z

namespace Stacks.Chow

variable {R : Type u} {S : Type v}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  {F : Type w} {E : Type z} [Field F] [Field E]
  [Algebra R F] [IsFractionRing R F] [Algebra S E] [IsFractionRing S E]
  (j : R →+* S) [IsLocalHom j] (f : F →+* E)
  (hf : ∀ r : R, f (algebraMap R F r) = algebraMap S E (j r))
  {π : R}

include hf

omit [IsLocalHom j] in
/-- The actual fraction-unit orders agree under an unramified local map. -/
theorem dvrFracOrd_map_across (hπ : Irreducible π) (hjπ : Irreducible (j π)) (x : Fˣ) :
    dvrFracOrd hjπ (Units.map f.toMonoidHom x) = dvrFracOrd hπ x := by
  obtain ⟨a, ha, -⟩ := exists_eq_unit_mul_zpow hπ x
  apply dvrFracOrd_eq_of_eq (u := Units.map j.toMonoidHom a) hjπ
  change f (x : F) = _
  rw [ha, map_mul, map_zpow₀, hf, hf]
  rfl

private theorem map_main_symbolProd (hπ : Irreducible π) (hjπ : Irreducible (j π))
    (l : List Fˣ) :
    milnorKRingMapLift (IsLocalRing.ResidueField.map j)
        (MilnorKShift.main (dvrMilnorShiftMap hπ (milnorKSymbolProd F l))) =
      MilnorKShift.main (dvrMilnorShiftMap hjπ
        (milnorKSymbolProd E (l.map (Units.map f.toMonoidHom)))) := by
  simp only [main_dvrMilnorShiftMap_symbolProd, milnorKRingMapLift_symbolProd, List.map_map]
  congr 1
  apply List.map_congr_left
  intro a _
  exact (dvrFracUnitPart_map j f hf hπ hjπ a).symm

private theorem map_involution_main_symbolProd (hπ : Irreducible π)
    (hjπ : Irreducible (j π)) (l : List Fˣ) :
    milnorKRingMapLift (IsLocalRing.ResidueField.map j)
        (milnorKInvolution (IsLocalRing.ResidueField R)
          (MilnorKShift.main (dvrMilnorShiftMap hπ (milnorKSymbolProd F l)))) =
      milnorKInvolution (IsLocalRing.ResidueField S)
        (MilnorKShift.main (dvrMilnorShiftMap hjπ
          (milnorKSymbolProd E (l.map (Units.map f.toMonoidHom))))) := by
  simp only [main_dvrMilnorShiftMap_symbolProd, milnorKInvolution_symbolProd,
    List.length_map, map_zsmul]
  congr 1
  simpa only [main_dvrMilnorShiftMap_symbolProd] using
    map_main_symbolProd j f hf hπ hjπ l

/-- On every list symbol the native shift coefficient commutes with unramified restriction. -/
theorem dvrMilnorShiftMap_shift_symbolProd_map_across (hπ : Irreducible π)
    (hjπ : Irreducible (j π)) (l : List Fˣ) :
    milnorKRingMapLift (IsLocalRing.ResidueField.map j)
        (MilnorKShift.shift (dvrMilnorShiftMap hπ (milnorKSymbolProd F l))) =
      MilnorKShift.shift (dvrMilnorShiftMap hjπ
        (milnorKSymbolProd E (l.map (Units.map f.toMonoidHom)))) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, milnorKSymbolProd_cons, map_mul, MilnorKShift.shift_mul,
      dvrMilnorShiftMap_milnorKSymbol, main_dvrMilnorThetaHom, shift_dvrMilnorThetaHom,
      map_add, map_zsmul, map_one, milnorKRingMapLift_symbol]
    rw [ih, map_involution_main_symbolProd j f hf hπ hjπ l,
      dvrFracOrd_map_across j f hf hπ hjπ, dvrFracUnitPart_map j f hf hπ hjπ]
    congr 2
    simp [milnorKNegOne_eq]

/-- The all-degree residue square for unramified field maps and specified uniformizers. -/
theorem dvrMilnorTameSymbol_map_across (hπ : Irreducible π) (hjπ : Irreducible (j π)) (n : ℕ) :
    (milnorKTheoryMap (IsLocalRing.ResidueField.map j) n).toAddMonoidHom.comp
        (dvrMilnorTameSymbol (F := F) hπ n) =
      (dvrMilnorTameSymbol (F := E) hjπ n).comp (milnorKTheoryMap f (n + 1)).toAddMonoidHom := by
  apply milnorKTheory_addHom_ext
  intro a
  apply Subtype.ext
  simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
    milnorKTheoryMap_tupleSymbol]
  rw [← milnorKRingMapLift_coe]
  change milnorKRingMapLift (IsLocalRing.ResidueField.map j)
      (MilnorKShift.shift (dvrMilnorShiftMap hπ (milnorKSymbolProd F (List.ofFn a)))) =
    MilnorKShift.shift (dvrMilnorShiftMap hjπ (milnorKSymbolProd E
      (List.ofFn (Units.map f.toMonoidHom ∘ a))))
  simpa only [List.map_ofFn, Function.comp_def] using
    dvrMilnorShiftMap_shift_symbolProd_map_across j f hf hπ hjπ (List.ofFn a)

end Stacks.Chow

attribute [colib_tag "COL-0113"] Stacks.Chow.dvrFracOrd_map_across
  Stacks.Chow.dvrMilnorShiftMap_shift_symbolProd_map_across
  Stacks.Chow.dvrMilnorTameSymbol_map_across

add_to_stacks 0EAY "DVR tame-symbol background; four-universe specified e=1 formula proved here"
  Stacks.Chow.dvrMilnorTameSymbol_map_across
