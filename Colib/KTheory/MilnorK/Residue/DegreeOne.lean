/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.Chow.DvrTameSymbol.MilnorTameSymbol
public import Colib.Util.References
public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.MilnorKDegreeOne
public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.MilnorKDegreeZero

/-!
# Degree-one residue and its kernel

Under the native identifications `K₁(F) = Fˣ` and `K₀(κ) = ℤ`, the native DVR residue is the
integer order. Its kernel consists exactly of the classes corresponding to actual units of
the DVR. This uses the native fraction-unit decomposition, not a second valuation or K-group model.

The order formula adapts the actual-DVR case of `MilnorK.zeroEquiv_residue` in
`Aglib.KTheory.MilnorK.Residue.Basic` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`, lines 188–197. The kernel characterization is a direct
consequence of this formula and the native order-zero/unit-lifting theorem. No uniformizer
independence proof or high-level norm dependency is required.
-/

@[expose] public noncomputable section

universe u v

namespace Stacks.Chow

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type v} [Field F] [Algebra R F] [IsFractionRing R F] {π : R}

/-- The native degree-one residue, identified with an integer, is the DVR order. -/
theorem milnorKTheoryZeroAddEquiv_dvrMilnorTameSymbol (hπ : Irreducible π)
    (x : MilnorKTheory F 1) :
    milnorKTheoryZeroAddEquiv (IsLocalRing.ResidueField R) (dvrMilnorTameSymbol hπ 0 x) =
      dvrFracOrd hπ (milnorKTheoryOneAddEquiv F x).toMul := by
  have hx : (x : MilnorKRing F) =
      milnorKSymbol F (milnorKTheoryOneAddEquiv F x).toMul := by
    simpa only [AddEquiv.symm_apply_apply, milnorKSymbol_eq_mk', ofMul_toMul] using
      coe_milnorKTheoryOneAddEquiv_symm F (milnorKTheoryOneAddEquiv F x)
  have hy : dvrMilnorTameSymbol hπ 0 x =
      milnorKZeroMap (IsLocalRing.ResidueField R)
        (dvrFracOrd hπ (milnorKTheoryOneAddEquiv F x).toMul) := by
    apply Subtype.ext
    rw [dvrMilnorTameSymbol_coe, hx, dvrMilnorShiftMap_milnorKSymbol,
      shift_dvrMilnorThetaHom]
    change _ = (milnorKSteinbergIdeal (IsLocalRing.ResidueField R)).ringCon.mk'
      (algebraMap ℤ (MilnorKTensorAlgebra (IsLocalRing.ResidueField R)) _)
    rw [Algebra.algebraMap_eq_smul_one, map_zsmul, map_one]
  rw [hy, milnorKTheoryZeroAddEquiv_milnorKZeroMap]

/-- A degree-one class has zero residue exactly when its associated unit comes from the DVR. -/
theorem dvrMilnorTameSymbol_one_eq_zero_iff (hπ : Irreducible π)
    (x : MilnorKTheory F 1) :
    dvrMilnorTameSymbol hπ 0 x = 0 ↔
      ∃ a : Rˣ, (milnorKTheoryOneAddEquiv F x).toMul =
        Units.map (algebraMap R F).toMonoidHom a := by
  have hz : dvrMilnorTameSymbol hπ 0 x = 0 ↔
      dvrFracOrd hπ (milnorKTheoryOneAddEquiv F x).toMul = 0 := by
    rw [← milnorKTheoryZeroAddEquiv_dvrMilnorTameSymbol hπ x]
    constructor
    · intro h
      rw [h, map_zero]
    · intro h
      apply (milnorKTheoryZeroAddEquiv (IsLocalRing.ResidueField R)).injective
      simpa only [map_zero] using h
  rw [hz]
  constructor
  · intro h
    obtain ⟨a, ha, -⟩ := exists_val_eq_algebraMap_of_dvrFracOrd_eq_zero hπ h
    exact ⟨a, Units.ext ha⟩
  · rintro ⟨a, ha⟩
    rw [ha]
    exact dvrFracOrd_unitsMap hπ a

/-- The canonical degree-one residue has exactly the actual DVR units as its kernel. -/
theorem dvrMilnorTameSymbol'_one_eq_zero_iff (x : MilnorKTheory F 1) :
    dvrMilnorTameSymbol' R F 0 x = 0 ↔
      ∃ a : Rˣ, (milnorKTheoryOneAddEquiv F x).toMul =
        Units.map (algebraMap R F).toMonoidHom a :=
  dvrMilnorTameSymbol_one_eq_zero_iff
    (IsDiscreteValuationRing.exists_irreducible R).choose_spec x

end Stacks.Chow

attribute [colib_tag "COL-0139"] Stacks.Chow.milnorKTheoryZeroAddEquiv_dvrMilnorTameSymbol
  Stacks.Chow.dvrMilnorTameSymbol_one_eq_zero_iff Stacks.Chow.dvrMilnorTameSymbol'_one_eq_zero_iff

attribute [stacks 0EAY "DVR tame-symbol background; native degree-one order and kernel proved here"]
  Stacks.Chow.milnorKTheoryZeroAddEquiv_dvrMilnorTameSymbol
