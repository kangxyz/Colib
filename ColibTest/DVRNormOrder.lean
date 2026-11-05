/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.Norm.DVROrder

/-!
# Consumers of the native ordinary norm-order theorem

These extend the mathematical consumers of `AglibTest/DVRNormValuation.lean`
at revision `101dbb8564fb0e29f28cfcb79168d878b5ab489f`, SHA-256
`285588b242d7867cd4779f3b246f2808742a4579e991bcd6f9f5736228ca597d`.
The selected carrier is native `dvrFracOrd`, not the old Aglib K2 order.
No PerfectField, henselianity, exponent invertibility, prime degree, or chosen
integral-closure instance is supplied in these tests.
-/

noncomputable section

open IsLocalRing Stacks.Chow

universe u v w z

namespace ColibTest.DVRNormOrder

variable (R : Type u) (S : Type v) (F : Type w) (E : Type z)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
  [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  [FiniteDimensional F E]
  {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)

/-- The actual ring unit norm is retained, not an abstract unit existence witness. -/
theorem actual_unit_norm (a : Sˣ) :
    Units.map (Algebra.norm F) (Units.map (algebraMap S E).toMonoidHom a) =
      Units.map (algebraMap R F).toMonoidHom (Units.map (Algebra.intNorm R S) a) :=
  Algebra.norm_unitsMap_eq_intNorm R S F E a

/-- Ring units have norm order zero. -/
theorem ring_unit_order (a : Sˣ) :
    dvrFracOrd hπ
      (Units.map (Algebra.norm F) (Units.map (algebraMap S E).toMonoidHom a)) = 0 :=
  dvrFracOrd_norm_unitsMap R S F E hπ a

/-- The exact integer equation is visible before cancelling the ramification exponent. -/
theorem integer_relation (a : Sˣ) (e : ℕ)
    (he : algebraMap R S π = (a : S) * ϖ ^ e) :
    (e : ℤ) * dvrFracOrd hπ (Units.map (Algebra.norm F) (dvrFracUniformizer E hϖ)) =
      (Module.finrank F E : ℤ) :=
  ramification_mul_dvrFracOrd_norm_uniformizer R S F E hπ hϖ a e he

/-- The actual equation supplies a nonzero exponent, without a separate nonzero premise. -/
theorem equation_uniformizer (a : Sˣ) (e : ℕ)
    (he : algebraMap R S π = (a : S) * ϖ ^ e) :
    dvrFracOrd hπ (Units.map (Algebra.norm F) (dvrFracUniformizer E hϖ)) =
      (Module.finrank (ResidueField R) (ResidueField S) : ℤ) :=
  dvrFracOrd_norm_uniformizer_of_equation R S F E hπ hϖ a e he

/-- The exponent may equal the residue characteristic; no inverse exponent is used.
The named instance fixes the characteristic without becoming a mathematical premise of the proof. -/
theorem residue_characteristic_exponent (p : ℕ)
    [_residueCharacteristicP : CharP (ResidueField S) p] (a : Sˣ)
    (he : algebraMap R S π = (a : S) * ϖ ^ p) :
    dvrFracOrd hπ (Units.map (Algebra.norm F) (dvrFracUniformizer E hϖ)) =
      (Module.finrank (ResidueField R) (ResidueField S) : ℤ) :=
  dvrFracOrd_norm_uniformizer_of_equation R S F E hπ hϖ a p he

/-- The general uniformizer theorem needs no supplied ramification presentation. -/
theorem constructed_uniformizer_equation :
    dvrFracOrd hπ (Units.map (Algebra.norm F) (dvrFracUniformizer E hϖ)) =
      (Module.finrank (ResidueField R) (ResidueField S) : ℤ) :=
  dvrFracOrd_norm_uniformizer R S F E hπ hϖ

/-- Arbitrary nonzero field elements include both units and poles. -/
theorem arbitrary_field_norm (x : Eˣ) :
    dvrFracOrd hπ (Units.map (Algebra.norm F) x) =
      (Module.finrank (ResidueField R) (ResidueField S) : ℤ) * dvrFracOrd hϖ x :=
  dvrFracOrd_norm R S F E hπ hϖ x

/-- A genuine pole has norm order minus the residue degree. -/
theorem inverse_uniformizer_norm :
    dvrFracOrd hπ (Units.map (Algebra.norm F) (dvrFracUniformizer E hϖ)⁻¹) =
      -(Module.finrank (ResidueField R) (ResidueField S) : ℤ) := by
  rw [dvrFracOrd_norm R S F E hπ hϖ, dvrFracOrd_inv,
    dvrFracOrd_uniformizer, mul_neg_one]

/-- Arbitrary integer powers of the native uniformizer include every possible order. -/
theorem integer_uniformizer_norm (n : ℤ) :
    dvrFracOrd hπ (Units.map (Algebra.norm F) (dvrFracUniformizer E hϖ ^ n)) =
      (Module.finrank (ResidueField R) (ResidueField S) : ℤ) * n := by
  rw [dvrFracOrd_norm R S F E hπ hϖ, dvrFracOrd_zpow,
    dvrFracOrd_uniformizer, mul_one]

/-- An explicit nonzero element is handled without choosing a separate norm unit. -/
theorem nonzero_field_element (x : E) (hx : x ≠ 0) :
    dvrFracOrd hπ (Units.mk0 (Algebra.norm F x) (Algebra.norm_ne_zero_iff.mpr hx)) =
      (Module.finrank (ResidueField R) (ResidueField S) : ℤ) *
        dvrFracOrd hϖ (Units.mk0 x hx) :=
  dvrFracOrd_norm_mk0 R S F E hπ hϖ x hx

/-- The exact source-normalized valuation formula follows without PerfectField. -/
theorem source_order_norm (x : Eˣ) :
    -WithZero.log ((IsDiscreteValuationRing.maximalIdeal R).valuation F
      (Algebra.norm F (x : E))) =
      (Module.finrank (ResidueField R) (ResidueField S) : ℤ) *
        -WithZero.log ((IsDiscreteValuationRing.maximalIdeal S).valuation E (x : E)) :=
  neg_log_valuation_norm R S F E x

end ColibTest.DVRNormOrder
