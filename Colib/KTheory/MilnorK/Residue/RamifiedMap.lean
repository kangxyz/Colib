/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.MilnorK.Residue.RamifiedUnitPart
public import Colib.Util.References
public import Colib.KTheory.MilnorK.Residue.RamifiedOrder
public import Colib.KTheory.MilnorK.Residue.RamifiedShiftAlgebra
public import Colib.KTheory.MilnorK.Symbols.RingTransport
public import StacksFrontier.AlgebraicGeometry.Chow.DvrTameSymbol.MilnorTameSymbol

/-!
# Higher-degree ramified restriction with specified uniformizers

This adapts the actual DVR theorem `MilnorK.DVR.residue_ramified_restrict` from
`Aglib.KTheory.MilnorK.Residue.RamifiedRestriction`, revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`, lines 161–172. The native shift components
are compared simultaneously, retaining the angular-component correction. No second residue
model is introduced. The statement here uses specified uniformizers.
`Colib.KTheory.MilnorK.Residue.CanonicalRamifiedMap` derives independence from its
identity-map case and supplies the canonical chosen-uniformizer comparison.
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
  {π : R} {ρ : S}

include hf

/-- The two native components transform together; the main component retains its unit correction. -/
theorem dvrMilnorShiftMap_symbolProd_map_ramified (hπ : Irreducible π) (hρ : Irreducible ρ)
    (u : Sˣ) (e : ℕ) (hπmap : j π = (u : S) * ρ ^ e) (l : List Fˣ) :
    MilnorKShift.main (dvrMilnorShiftMap hρ
        (milnorKSymbolProd E (l.map (Units.map f.toMonoidHom)))) =
      milnorKRingMapLift (IsLocalRing.ResidueField.map j)
          (MilnorKShift.main (dvrMilnorShiftMap hπ (milnorKSymbolProd F l))) +
        milnorKRingMapLift (IsLocalRing.ResidueField.map j)
          (MilnorKShift.shift (dvrMilnorShiftMap hπ (milnorKSymbolProd F l))) *
            milnorKSymbol (IsLocalRing.ResidueField S)
              (Units.map (IsLocalRing.residue S).toMonoidHom u) ∧
    MilnorKShift.shift (dvrMilnorShiftMap hρ
        (milnorKSymbolProd E (l.map (Units.map f.toMonoidHom)))) =
      (e : ℤ) • milnorKRingMapLift (IsLocalRing.ResidueField.map j)
        (MilnorKShift.shift (dvrMilnorShiftMap hπ (milnorKSymbolProd F l))) := by
  have hN : milnorKRingMapLift (IsLocalRing.ResidueField.map j)
      (milnorKNegOne (IsLocalRing.ResidueField R)) =
        milnorKNegOne (IsLocalRing.ResidueField S) := by simp [milnorKNegOne_eq]
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l a ih =>
    constructor
    · simp only [List.map_append, List.map_singleton, milnorKSymbolProd_append,
        milnorKSymbolProd_singleton, map_mul, MilnorKShift.main_mul, MilnorKShift.shift_mul,
        dvrMilnorShiftMap_milnorKSymbol, main_dvrMilnorThetaHom, shift_dvrMilnorThetaHom,
        milnorKInvolution_milnorKSymbol, map_add, map_neg, map_zsmul,
        milnorKRingMapLift_symbol, hN, mul_smul_comm, smul_mul_assoc, mul_one, mul_neg]
      rw [ih.1, dvrFracUnitPart_map_ramified j f hf hπ hρ u e hπmap a,
        milnorKSymbol_mul, milnorKSymbol_zpow]
      simpa only [sub_eq_add_neg] using
        milnorK_ramified_main_recursion
          (milnorKRingMapLift (IsLocalRing.ResidueField.map j)
            (MilnorKShift.main (dvrMilnorShiftMap hπ (milnorKSymbolProd F l))))
          (milnorKRingMapLift (IsLocalRing.ResidueField.map j)
            (MilnorKShift.shift (dvrMilnorShiftMap hπ (milnorKSymbolProd F l))))
          (Units.map (IsLocalRing.ResidueField.map j).toMonoidHom (dvrFracUnitPart hπ a))
          (Units.map (IsLocalRing.residue S).toMonoidHom u) (dvrFracOrd hπ a)
    · simp only [List.map_append, List.map_singleton, milnorKSymbolProd_append,
        milnorKSymbolProd_singleton, map_mul, MilnorKShift.shift_mul,
        dvrMilnorShiftMap_milnorKSymbol, main_dvrMilnorThetaHom, shift_dvrMilnorThetaHom,
        milnorKInvolution_milnorKSymbol, map_add, map_neg, map_zsmul,
        milnorKRingMapLift_symbol, hN, mul_smul_comm, smul_mul_assoc, mul_one, mul_neg]
      rw [ih.1, ih.2, dvrFracOrd_map_ramified j f hf hπ hρ u e hπmap a,
        dvrFracUnitPart_map_ramified j f hf hπ hρ u e hπmap a,
        milnorKSymbol_mul, milnorKSymbol_zpow]
      simpa only [sub_eq_add_neg, smul_mul_assoc, smul_smul, mul_assoc,
        mul_left_comm, mul_comm] using
        milnorK_ramified_shift_recursion
          (milnorKRingMapLift (IsLocalRing.ResidueField.map j)
            (MilnorKShift.main (dvrMilnorShiftMap hπ (milnorKSymbolProd F l))))
          (milnorKRingMapLift (IsLocalRing.ResidueField.map j)
            (MilnorKShift.shift (dvrMilnorShiftMap hπ (milnorKSymbolProd F l))))
          (milnorKSymbol (IsLocalRing.ResidueField S)
            (Units.map (IsLocalRing.ResidueField.map j).toMonoidHom (dvrFracUnitPart hπ a)))
          (milnorKSymbol (IsLocalRing.ResidueField S)
            (Units.map (IsLocalRing.residue S).toMonoidHom u)) (dvrFracOrd hπ a) e

/-- Ramification multiplies the specified-uniformizer residue in every homogeneous degree. -/
theorem dvrMilnorTameSymbol_map_ramified (hπ : Irreducible π) (hρ : Irreducible ρ)
    (u : Sˣ) (e : ℕ) (hπmap : j π = (u : S) * ρ ^ e) (n : ℕ) :
    (dvrMilnorTameSymbol (F := E) hρ n).comp (milnorKTheoryMap f (n + 1)).toAddMonoidHom =
      (e : ℤ) • ((milnorKTheoryMap (IsLocalRing.ResidueField.map j) n).toAddMonoidHom.comp
        (dvrMilnorTameSymbol (F := F) hπ n)) := by
  apply milnorKTheory_addHom_ext
  intro a
  apply Subtype.ext
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.smul_apply, LinearMap.toAddMonoidHom_coe,
    milnorKTheoryMap_tupleSymbol, AddSubgroup.coe_zsmul]
  rw [← milnorKRingMapLift_coe]
  change MilnorKShift.shift (dvrMilnorShiftMap hρ (milnorKSymbolProd E
      (List.ofFn (Units.map f.toMonoidHom ∘ a)))) =
    (e : ℤ) • milnorKRingMapLift (IsLocalRing.ResidueField.map j)
      (MilnorKShift.shift (dvrMilnorShiftMap hπ (milnorKSymbolProd F (List.ofFn a))))
  simpa only [List.map_ofFn, Function.comp_def] using
    (dvrMilnorShiftMap_symbolProd_map_ramified j f hf hπ hρ u e hπmap (List.ofFn a)).2

end Stacks.Chow

attribute [colib_tag "COL-0143"] Stacks.Chow.dvrFracUnitPart_map_ramified
  Stacks.Chow.dvrMilnorShiftMap_symbolProd_map_ramified
  Stacks.Chow.dvrMilnorTameSymbol_map_ramified

attribute [stacks 0EAY "DVR tame-symbol background; specified ramified comparison proved here"]
  Stacks.Chow.dvrMilnorTameSymbol_map_ramified
