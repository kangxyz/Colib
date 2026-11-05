/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import StacksFrontier.AlgebraicGeometry.Chow.DvrTameSymbol.FractionUnits

/-!
# Native fraction orders and the maximal-ideal valuation

The selected integer order is the existing `Stacks.Chow.dvrFracOrd`. This file
adds power and inverse formulas and identifies it with the negative logarithm
of the native maximal-ideal valuation. No new order, uniformizer unit, or
additive-homomorphism model is introduced.

## Source provenance

This replaces the order helpers in `Aglib/RingTheory/DVRNormValuation.lean`,
lines 36--77, at revision `101dbb8564fb0e29f28cfcb79168d878b5ab489f`, SHA-256
`af15a6a5c883bdbc7a94075e5380ddd41467e9926ebd24d858c56368fdc35da7`.
The original module is `Motivic.Aglib.RingTheory.DVRNormValuation`, with source SHA-256
`7e08e6503d336988192dfe1bf904f8a2f523f9479c316a8bdb66d2ddb28a87e7`.
The comparison theorem states the old order expression directly, without
importing or reproducing its definition. Native fraction-unit decomposition
and its uniqueness remain owned by pinned Stacks.
-/

@[expose] public noncomputable section

open scoped WithZero

universe u v

namespace Stacks.Chow

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type v} [Field F] [Algebra R F] [IsFractionRing R F] {π ρ : R}

/-- The native integer order sends an integer power to the corresponding multiple. -/
@[colib_tag "COL-0200"]
theorem dvrFracOrd_zpow (hπ : Irreducible π) (x : Fˣ) (n : ℤ) :
    dvrFracOrd hπ (x ^ n) = n * dvrFracOrd hπ x := by
  unfold dvrFracOrd
  rw [map_zpow]
  change Multiplicative.toAdd (((dvrFracUnitsEquiv F hπ).symm x).2 ^ n) =
    n * Multiplicative.toAdd ((dvrFracUnitsEquiv F hπ).symm x).2
  simpa only [zsmul_eq_mul, Int.cast_id] using
    toAdd_zpow ((dvrFracUnitsEquiv F hπ).symm x).2 n

/-- Natural powers are included with the literal integer cast of their exponent. -/
theorem dvrFracOrd_pow (hπ : Irreducible π) (x : Fˣ) (n : ℕ) :
    dvrFracOrd hπ (x ^ n) = (n : ℤ) * dvrFracOrd hπ x := by
  simpa only [zpow_natCast] using dvrFracOrd_zpow hπ x (n : ℤ)

/-- Inversion negates the native integer order, including genuine poles. -/
theorem dvrFracOrd_inv (hπ : Irreducible π) (x : Fˣ) :
    dvrFracOrd hπ x⁻¹ = -dvrFracOrd hπ x := by
  simpa only [zpow_neg_one, neg_one_mul] using dvrFracOrd_zpow hπ x (-1)

/-- The chosen native fraction-field uniformizer has normalized order one. -/
theorem dvrFracOrd_uniformizer (hπ : Irreducible π) :
    dvrFracOrd hπ (dvrFracUniformizer F hπ) = 1 :=
  dvrFracOrd_eq_of_eq (u := 1) (n := 1) hπ (by simp)

/-- The native order is exactly the negative logarithm of the actual maximal-ideal
valuation. This identifies the original source expression, including negative orders. -/
@[colib_tag "COL-0200",
  colib_ref "aglib_principal_euler_pin" "RingTheory/DVRNormValuation.lean:36-77"
    "adaptation" "Native fraction order equals the actual negative valuation logarithm"]
theorem dvrFracOrd_eq_neg_log_valuation (hπ : Irreducible π) (x : Fˣ) :
    dvrFracOrd hπ x =
      -WithZero.log ((IsDiscreteValuationRing.maximalIdeal R).valuation F (x : F)) := by
  obtain ⟨a, ha, -⟩ := exists_eq_unit_mul_zpow hπ x
  have hva : (IsDiscreteValuationRing.maximalIdeal R).valuation F
      (algebraMap R F (a : R)) = 1 := by
    simp [IsDiscreteValuationRing.maximalIdeal]
  have hvπ : (IsDiscreteValuationRing.maximalIdeal R).valuation F
      (algebraMap R F π) = WithZero.exp (-1 : ℤ) := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact (IsDiscreteValuationRing.maximalIdeal R).intValuation_singleton hπ.ne_zero
      hπ.maximalIdeal_eq
  rw [ha, map_mul, map_zpow₀, hva, one_mul, hvπ,
    WithZero.log_zpow, WithZero.log_exp]
  simp

/-- Changing the irreducible used to present a fraction unit does not change its order. -/
@[colib_tag "COL-0200"]
theorem dvrFracOrd_eq_of_irreducible (hπ : Irreducible π) (hρ : Irreducible ρ) (x : Fˣ) :
    dvrFracOrd hπ x = dvrFracOrd hρ x := by
  rw [dvrFracOrd_eq_neg_log_valuation hπ, dvrFracOrd_eq_neg_log_valuation hρ]

end Stacks.Chow
