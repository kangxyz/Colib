/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.DiscreteValuationRing.FractionOrder

/-!
# Native fraction-order consumers

These consumers use the existing native order and uniformizer units, compare
the source's valuation-log expression, and retain genuine negative orders.
They introduce no old Aglib valuation or Milnor model.
-/

noncomputable section

universe u v

open Stacks.Chow

namespace ColibTest.DVRFractionOrder

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type v} [Field F] [Algebra R F] [IsFractionRing R F]
  {π ρ : R} (hπ : Irreducible π)

/-- Arbitrary integer powers, with their signed exponent. -/
theorem integer_power (x : Fˣ) (n : ℤ) :
    dvrFracOrd hπ (x ^ n) = n * dvrFracOrd hπ x :=
  dvrFracOrd_zpow hπ x n

/-- Inversion covers both signs of the order. -/
theorem inverse (x : Fˣ) : dvrFracOrd hπ x⁻¹ = -dvrFracOrd hπ x :=
  dvrFracOrd_inv hπ x

/-- The native fraction unit of the actual irreducible has order one. -/
theorem actual_uniformizer : dvrFracOrd hπ (dvrFracUniformizer F hπ) = 1 :=
  dvrFracOrd_uniformizer hπ

/-- The square is a nonunit of order two. -/
theorem uniformizer_square : dvrFracOrd hπ (dvrFracUniformizer F hπ ^ 2) = 2 := by
  rw [dvrFracOrd_pow, dvrFracOrd_uniformizer, mul_one]
  norm_num

/-- An inverse uniformizer is a pole of order minus one. -/
theorem inverse_uniformizer : dvrFracOrd hπ (dvrFracUniformizer F hπ)⁻¹ = -1 := by
  rw [dvrFracOrd_inv, dvrFracOrd_uniformizer]

/-- An arbitrary actual ring unit has order zero without any field-extension data. -/
theorem ring_unit (a : Rˣ) :
    dvrFracOrd hπ (Units.map (algebraMap R F).toMonoidHom a) = 0 :=
  dvrFracOrd_eq_of_eq (u := a) (n := 0) hπ (by simp)

/-- The original logarithmic normalization is preserved as a literal formula. -/
theorem source_normalization (x : Fˣ) :
    dvrFracOrd hπ x =
      -WithZero.log ((IsDiscreteValuationRing.maximalIdeal R).valuation F (x : F)) :=
  dvrFracOrd_eq_neg_log_valuation hπ x

/-- The order does not depend on the chosen uniformizer. -/
theorem uniformizer_independence (hρ : Irreducible ρ) (x : Fˣ) :
    dvrFracOrd hπ x = dvrFracOrd hρ x :=
  dvrFracOrd_eq_of_irreducible hπ hρ x

end ColibTest.DVRFractionOrder
