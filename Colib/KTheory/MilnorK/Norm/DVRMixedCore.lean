/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.MilnorK.Residue.RamifiedMap
public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.FieldNorm

/-!
# Native shift calculation for mixed norm–residue symbols

The existing ramified component formulas extend from symbol products to arbitrary elements
of the same native Milnor ring. The mixed norm square follows from explicit norm-order and
angular-component equalities. Its final discrepancy is twice a multiple of the native {-1}
symbol, so no ramification index is cancelled and no Milnor-group torsion-freeness is assumed.
The arithmetic premises are discharged in a separate concrete DVR leaf. No assertion is made
that mixed classes generate the original Milnor group.

UNCOMPILED SOURCE DRAFT. No Lean/Lake command has been run on this file.
-/

@[expose] public noncomputable section

universe u v

namespace Stacks.Chow

/-- The final discrepancy is twice a multiple of the native {-1} symbol. -/
theorem milnorK_norm_ramified_mixed_algebra {k : Type u} [Field k]
    (M B A U : MilnorKRing k) (e d r : ℤ) :
    (d * r) • M - B * (e • A + r • ((d * (e - 1)) • milnorKNegOne k - U)) +
        (d * r) • (B * milnorKNegOne k) =
      (d * r) • M - e • (B * A) + r • (B * U) +
        (e * r * d) • (B * milnorKNegOne k) := by
  calc
    _ = ((d * r) • M - e • (B * A) + r • (B * U) +
          (e * r * d) • (B * milnorKNegOne k)) +
        (d * r * (1 - e)) • ((2 : ℤ) • (B * milnorKNegOne k)) := by
      simp only [mul_add, mul_sub, mul_smul_comm, smul_sub, smul_smul]
      module
    _ = _ := by
      rw [two_smul, mul_milnorKNegOne_add_self, smul_zero, add_zero]

section Ramified

variable {R S : Type u}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  {F E : Type v} [Field F] [Field E]
  [Algebra R F] [IsFractionRing R F] [Algebra S E] [IsFractionRing S E]
  (j : R →+* S) [IsLocalHom j] (f : F →+* E)
  (hf : ∀ a : R, f (algebraMap R F a) = algebraMap S E (j a))
  {π : R} {ρ : S}

include hf in
/-- Simultaneous native component formulas for every element of the Milnor ring. -/
theorem dvrMilnorShiftMap_map_ramified
    (hπ : Irreducible π) (hρ : Irreducible ρ)
    (c : Sˣ) (e : ℕ) (hπmap : j π = (c : S) * ρ ^ e) (z : MilnorKRing F) :
    MilnorKShift.main (dvrMilnorShiftMap hρ (milnorKRingMap f z)) =
      milnorKRingMap (IsLocalRing.ResidueField.map j)
          (MilnorKShift.main (dvrMilnorShiftMap hπ z)) +
        milnorKRingMap (IsLocalRing.ResidueField.map j)
          (MilnorKShift.shift (dvrMilnorShiftMap hπ z)) *
            milnorKSymbol (IsLocalRing.ResidueField S)
              (Units.map (IsLocalRing.residue S).toMonoidHom c) ∧
    MilnorKShift.shift (dvrMilnorShiftMap hρ (milnorKRingMap f z)) =
      (e : ℤ) • milnorKRingMap (IsLocalRing.ResidueField.map j)
        (MilnorKShift.shift (dvrMilnorShiftMap hπ z)) := by
  let mR := (MilnorKShift.mainHom (IsLocalRing.ResidueField R)).comp
    (dvrMilnorShiftMap (F := F) hπ).toAddMonoidHom
  let bR := (MilnorKShift.shiftHom (IsLocalRing.ResidueField R)).comp
    (dvrMilnorShiftMap (F := F) hπ).toAddMonoidHom
  let mS := ((MilnorKShift.mainHom (IsLocalRing.ResidueField S)).comp
    (dvrMilnorShiftMap (F := E) hρ).toAddMonoidHom).comp (milnorKRingMap f).toAddMonoidHom
  let bS := ((MilnorKShift.shiftHom (IsLocalRing.ResidueField S)).comp
    (dvrMilnorShiftMap (F := E) hρ).toAddMonoidHom).comp (milnorKRingMap f).toAddMonoidHom
  let q := (milnorKRingMap (IsLocalRing.ResidueField.map j)).toAddMonoidHom
  let C := milnorKSymbol (IsLocalRing.ResidueField S)
    (Units.map (IsLocalRing.residue S).toMonoidHom c)
  let H : AddSubgroup (MilnorKRing F) :=
    mS.eqLocus (q.comp mR + (AddMonoidHom.mulRight C).comp (q.comp bR)) ⊓
      bS.eqLocus ((e : ℤ) • q.comp bR)
  have hH (l : List Fˣ) : milnorKSymbolProd F l ∈ H := by
    change
      MilnorKShift.main (dvrMilnorShiftMap hρ (milnorKRingMap f (milnorKSymbolProd F l))) =
        milnorKRingMap (IsLocalRing.ResidueField.map j)
            (MilnorKShift.main (dvrMilnorShiftMap hπ (milnorKSymbolProd F l))) +
          milnorKRingMap (IsLocalRing.ResidueField.map j)
            (MilnorKShift.shift (dvrMilnorShiftMap hπ (milnorKSymbolProd F l))) * C ∧
      MilnorKShift.shift (dvrMilnorShiftMap hρ (milnorKRingMap f (milnorKSymbolProd F l))) =
        (e : ℤ) • milnorKRingMap (IsLocalRing.ResidueField.map j)
          (MilnorKShift.shift (dvrMilnorShiftMap hπ (milnorKSymbolProd F l)))
    have ht := dvrMilnorShiftMap_symbolProd_map_ramified j f hf hπ hρ c e hπmap l
    simp only [← milnorKRingMapLift_symbolProd, milnorKRingMapLift_eq] at ht
    exact ht
  exact mem_of_forall_milnorKSymbolProd_mem hH z

/-- Appending one symbol to an arbitrary native Milnor-ring element. -/
theorem dvrMilnorShiftMap_shift_mul_symbol
    (hπ : Irreducible π) (z : MilnorKRing F) (a : Fˣ) :
    MilnorKShift.shift (dvrMilnorShiftMap hπ (z * milnorKSymbol F a)) =
      dvrFracOrd hπ a • MilnorKShift.main (dvrMilnorShiftMap hπ z) -
        MilnorKShift.shift (dvrMilnorShiftMap hπ z) *
          milnorKSymbol (IsLocalRing.ResidueField R) (dvrFracUnitPart hπ a) +
        dvrFracOrd hπ a •
          (MilnorKShift.shift (dvrMilnorShiftMap hπ z) *
            milnorKNegOne (IsLocalRing.ResidueField R)) := by
  simp only [map_mul, MilnorKShift.shift_mul, dvrMilnorShiftMap_milnorKSymbol,
    main_dvrMilnorThetaHom, shift_dvrMilnorThetaHom, milnorKInvolution_milnorKSymbol,
    mul_smul_comm, smul_mul_assoc, mul_one, mul_neg, sub_eq_add_neg]

include hf in
/-- The ramified mixed-symbol formula, with no homogeneity restriction on the prefix. -/
theorem dvrMilnorShiftMap_shift_map_mul_symbol
    (hπ : Irreducible π) (hρ : Irreducible ρ)
    (c : Sˣ) (e : ℕ) (hπmap : j π = (c : S) * ρ ^ e) (z : MilnorKRing F) (b : Eˣ) :
    let M := MilnorKShift.main (dvrMilnorShiftMap hπ z)
    let B := MilnorKShift.shift (dvrMilnorShiftMap hπ z)
    let q := milnorKRingMap (IsLocalRing.ResidueField.map j)
    let r := dvrFracOrd hρ b
    MilnorKShift.shift (dvrMilnorShiftMap hρ (milnorKRingMap f z * milnorKSymbol E b)) =
      r • q M - (e : ℤ) •
          (q B * milnorKSymbol (IsLocalRing.ResidueField S) (dvrFracUnitPart hρ b)) +
        r • (q B * milnorKSymbol (IsLocalRing.ResidueField S)
          (Units.map (IsLocalRing.residue S).toMonoidHom c)) +
        ((e : ℤ) * r) • (q B * milnorKNegOne (IsLocalRing.ResidueField S)) := by
  dsimp only
  rw [dvrMilnorShiftMap_shift_mul_symbol]
  obtain ⟨hmain, hshift⟩ := dvrMilnorShiftMap_map_ramified j f hf hπ hρ c e hπmap z
  rw [hmain, hshift]
  simp only [smul_add, smul_mul_assoc, smul_smul]
  module

end Ramified

section Norm

variable {R S : Type u}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  {F E : Type v} [Field F] [Field E]
  [Algebra R F] [IsFractionRing R F] [Algebra S E] [IsFractionRing S E]
  [Algebra F E] [FiniteDimensional F E]
  [Algebra (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)]
  [FiniteDimensional (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)]
  (j : R →+* S) [IsLocalHom j]
  (hf : ∀ a : R, algebraMap F E (algebraMap R F a) = algebraMap S E (j a))
  (hκ : IsLocalRing.ResidueField.map j =
    algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))
  {π : R} {ρ : S}

include hf hκ in
/-- The chosen native norm square on a mixed class, with its arithmetic inputs explicit.
This does not assert that mixed classes generate the original Milnor group. -/
theorem dvrMilnorShiftMap_shift_norm_mixed
    (hπ : Irreducible π) (hρ : Irreducible ρ)
    (c : Sˣ) (e : ℕ) (hπmap : j π = (c : S) * ρ ^ e) (z : MilnorKRing F) (b : Eˣ)
    (hord : dvrFracOrd hπ (Units.map (Algebra.norm F : E →* F) b) =
      (Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) : ℤ) *
        dvrFracOrd hρ b)
    (hang : milnorKSymbol (IsLocalRing.ResidueField R)
        (dvrFracUnitPart hπ (Units.map (Algebra.norm F : E →* F) b)) =
      (e : ℤ) • milnorKNormRing (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
        (milnorKSymbol (IsLocalRing.ResidueField S) (dvrFracUnitPart hρ b)) +
      dvrFracOrd hρ b •
        (((Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) : ℤ) *
            ((e : ℤ) - 1)) • milnorKNegOne (IsLocalRing.ResidueField R) -
          milnorKNormRing (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
            (milnorKSymbol (IsLocalRing.ResidueField S)
              (Units.map (IsLocalRing.residue S).toMonoidHom c)))) :
    MilnorKShift.shift (dvrMilnorShiftMap hπ (milnorKNormRing F E
        (milnorKRingMap (algebraMap F E) z * milnorKSymbol E b))) =
      milnorKNormRing (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
        (MilnorKShift.shift (dvrMilnorShiftMap hρ
          (milnorKRingMap (algebraMap F E) z * milnorKSymbol E b))) := by
  have hneg : milnorKNormRing (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
      (milnorKNegOne (IsLocalRing.ResidueField S)) =
    (Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) : ℤ) •
      milnorKNegOne (IsLocalRing.ResidueField R) := by
    have hm : milnorKRingMap
        (algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))
        (milnorKNegOne (IsLocalRing.ResidueField R)) =
      milnorKNegOne (IsLocalRing.ResidueField S) := by simp [milnorKNegOne_eq]
    rw [← hm, milnorKNormRing_milnorKRingMap]
  rw [milnorKNormRing_map_mul, milnorKNormRing_milnorKSymbol,
    dvrMilnorShiftMap_shift_mul_symbol, hord, hang]
  rw [dvrMilnorShiftMap_shift_map_mul_symbol j (algebraMap F E) hf hπ hρ c e hπmap z b]
  rw [hκ]
  simp only [map_add, map_sub, map_zsmul, milnorKNormRing_milnorKRingMap,
    milnorKNormRing_map_mul, hneg, mul_smul_comm, smul_smul]
  simpa only [mul_comm (dvrFracOrd hρ b)
    (Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) : ℤ)] using
    milnorK_norm_ramified_mixed_algebra
    (MilnorKShift.main (dvrMilnorShiftMap hπ z))
    (MilnorKShift.shift (dvrMilnorShiftMap hπ z))
    (milnorKNormRing (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
      (milnorKSymbol (IsLocalRing.ResidueField S) (dvrFracUnitPart hρ b)))
    (milnorKNormRing (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
      (milnorKSymbol (IsLocalRing.ResidueField S)
        (Units.map (IsLocalRing.residue S).toMonoidHom c)))
    (e : ℤ) (Module.finrank
      (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) : ℤ) (dvrFracOrd hρ b)

end Norm

end Stacks.Chow
