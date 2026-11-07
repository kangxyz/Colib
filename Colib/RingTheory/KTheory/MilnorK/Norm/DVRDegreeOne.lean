/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Residue.DegreeOne
public import Colib.RingTheory.Norm.DVROrder
public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.FieldNorm

/-!
# The native norm–residue square in degree one

The chosen native FieldNorm acts on degree one by the ordinary field norm and on degree
zero by the extension degree. The existing integral norm-order theorem therefore proves
the actual canonical DVR residue square from degree one to degree zero.

The two ring universes agree, and the two fraction-field universes agree; these two universes
remain independent. No prime degree, normality, perfectness, henselianity, tame ramification,
or torsion-freeness of a Milnor group is assumed. No higher-degree square or tower law follows
from this statement. All maps and equivalences are the existing native ones.

-/

@[expose] public noncomputable section

universe u v

namespace Stacks.Chow

private theorem coe_zeroMap_eq_zsmul_one
    (K : Type u) [Field K] (n : ℤ) :
    (milnorKZeroMap K n : MilnorKRing K) =
      n • (1 : MilnorKRing K) := by
  change (milnorKSteinbergIdeal K).ringCon.mk'
    (algebraMap ℤ (MilnorKTensorAlgebra K) n) = _
  rw [Algebra.algebraMap_eq_smul_one, map_zsmul, map_one]

private theorem coe_oneEquiv_symm_eq_symbol
    (K : Type u) [Field K] (a : Additive Kˣ) :
    ((milnorKTheoryOneAddEquiv K).symm a : MilnorKRing K) =
      milnorKSymbol K a.toMul := by
  rw [coe_milnorKTheoryOneAddEquiv_symm, milnorKSymbol_eq_mk']
  rfl

/-- The existing degree-one equivalence reads the chosen native norm as the unit norm. -/
theorem milnorKTheoryOneAddEquiv_milnorKNorm
    (K L : Type u) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L]
    (x : MilnorKTheory L 1) :
    (milnorKTheoryOneAddEquiv K (milnorKNorm K L 1 x)).toMul =
      Units.map (Algebra.norm K : L →* K)
        (milnorKTheoryOneAddEquiv L x).toMul := by
  let a : Lˣ := (milnorKTheoryOneAddEquiv L x).toMul
  have hx : (x : MilnorKRing L) = milnorKSymbol L a := by
    simpa only [AddEquiv.symm_apply_apply] using
      coe_oneEquiv_symm_eq_symbol L (milnorKTheoryOneAddEquiv L x)
  have h :
      milnorKNorm K L 1 x =
        (milnorKTheoryOneAddEquiv K).symm
          (Additive.ofMul (Units.map (Algebra.norm K : L →* K) a)) := by
    apply Subtype.ext
    rw [coe_milnorKNorm, hx, milnorKNormRing_milnorKSymbol,
      coe_oneEquiv_symm_eq_symbol]
    rfl
  rw [h, AddEquiv.apply_symm_apply]
  rfl

/-- The existing degree-zero equivalence reads the chosen native norm as degree multiplication. -/
theorem milnorKTheoryZeroAddEquiv_milnorKNorm
    (K L : Type u) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L]
    (x : MilnorKTheory L 0) :
    milnorKTheoryZeroAddEquiv K (milnorKNorm K L 0 x) =
      (Module.finrank K L : ℤ) * milnorKTheoryZeroAddEquiv L x := by
  obtain ⟨n, rfl⟩ := milnorKZeroMap_surjective L x
  have h :
      milnorKNorm K L 0 (milnorKZeroMap L n) =
        milnorKZeroMap K ((Module.finrank K L : ℤ) * n) := by
    apply Subtype.ext
    rw [coe_milnorKNorm, coe_zeroMap_eq_zsmul_one,
      map_zsmul, milnorKNormRing_one, coe_zeroMap_eq_zsmul_one, smul_smul]
    rw [mul_comm n]
  rw [h, milnorKTheoryZeroAddEquiv_milnorKZeroMap,
    milnorKTheoryZeroAddEquiv_milnorKZeroMap]

variable (R S : Type u) (F E : Type v)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [IsLocalHom (algebraMap R S)]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
  [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [FiniteDimensional F E]

/-- The actual canonical tame residue commutes with the native norm from degree one to zero. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_one
    (x : MilnorKTheory E 1) :
    dvrMilnorTameSymbol' R F 0 (milnorKNorm F E 1 x) =
      milnorKNorm (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField S) 0
        (dvrMilnorTameSymbol' S E 0 x) := by
  apply (milnorKTheoryZeroAddEquiv (IsLocalRing.ResidueField R)).injective
  rw [milnorKTheoryZeroAddEquiv_milnorKNorm]
  change
    milnorKTheoryZeroAddEquiv (IsLocalRing.ResidueField R)
      (dvrMilnorTameSymbol (F := F)
        (IsDiscreteValuationRing.exists_irreducible R).choose_spec 0
        (milnorKNorm F E 1 x)) =
    (Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S) : ℤ) *
    milnorKTheoryZeroAddEquiv (IsLocalRing.ResidueField S)
      (dvrMilnorTameSymbol (F := E)
        (IsDiscreteValuationRing.exists_irreducible S).choose_spec 0 x)
  rw [milnorKTheoryZeroAddEquiv_dvrMilnorTameSymbol,
    milnorKTheoryZeroAddEquiv_dvrMilnorTameSymbol,
    milnorKTheoryOneAddEquiv_milnorKNorm]
  exact dvrFracOrd_norm R S F E
    (IsDiscreteValuationRing.exists_irreducible R).choose_spec
    (IsDiscreteValuationRing.exists_irreducible S).choose_spec
    (milnorKTheoryOneAddEquiv E x).toMul

/-- The degree-one square as equality of the existing native additive maps. -/
theorem dvrMilnorTameSymbol'_comp_milnorKNorm_one :
    (dvrMilnorTameSymbol' R F 0).comp (milnorKNorm F E 1) =
      (milnorKNorm (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField S) 0).comp
        (dvrMilnorTameSymbol' S E 0) := by
  apply AddMonoidHom.ext
  intro x
  exact dvrMilnorTameSymbol'_milnorKNorm_one R S F E x

end Stacks.Chow
