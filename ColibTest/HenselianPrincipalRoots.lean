/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.Henselian.PrincipalRoots

/-!
# Principal-root consumers

These consumers use roots in the original ring and its actual unit group.
They check arbitrary principal elements, literal maximal-ideal perturbations of
`1`, the exponent `1`, mixed characteristic with an invertible exponent, and
the residue-characteristic-zero specialization. Final validation separately
audits the actual transitive axiom closure.

Adapted from `AglibTest/HenselianPrincipalRoots.lean` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`, SHA-256
`1d73308cc36d20da88fc40839469e9b87e18eaa1e1f1ec99dedc05f072e7f305`.
-/

noncomputable section

open IsLocalRing HenselianLocalRing.PrincipalRoots

namespace ColibTest.HenselianPrincipalRoots

variable {R : Type*} [CommRing R] [HenselianLocalRing R]

/-- The root is a unit of the original ring, with the exact desired power. -/
theorem actual_unit_root (n : ℕ) (hn : 0 < n) (hnunit : IsUnit (n : R))
    (h : Rˣ) (hh : residue R (h : R) = 1) :
    ∃ y : Rˣ, residue R (y : R) = 1 ∧ y ^ n = h :=
  exists_pow_eq n hn hnunit h hh

/-- A literal principal element `1 + a` has a root in the original ring. -/
theorem maximalIdeal_perturbation (n : ℕ) (hn : 0 < n) (hnunit : IsUnit (n : R))
    (a : R) (ha : a ∈ maximalIdeal R) :
    ∃ y : Rˣ, residue R (y : R) = 1 ∧ (y : R) ^ n = 1 + a := by
  apply exists_unit_root n hn hnunit
  rw [map_add, map_one, (residue_eq_zero_iff a).mpr ha, add_zero]

/-- In exponent one, the constructed root is the given unit itself. -/
theorem exponent_one (h : Rˣ) (hh : residue R (h : R) = 1) :
    ∃ y : Rˣ, residue R (y : R) = 1 ∧ y = h := by
  simpa only [pow_one] using exists_pow_eq 1 (by decide) (by simp) h hh

/-- Mixed characteristic is allowed: the exponent `p + 1` reduces to `1`.
The explicitly unused instance keeps this regression in characteristic zero. -/
theorem mixed_characteristic_root [_mixedCharacteristicZero : CharZero R] (p : ℕ)
    [CharP (ResidueField R) p] (hp : 0 < p)
    (h : Rˣ) (hh : residue R (h : R) = 1) :
    ∃ y : Rˣ, residue R (y : R) = 1 ∧ y ^ (p + 1) = h := by
  have hpunit : IsUnit ((p + 1 : ℕ) : R) := by
    apply (residue_ne_zero_iff_isUnit _).mp
    simp
  exact exists_pow_eq (p + 1) (Nat.lt_trans hp (Nat.lt_succ_self p)) hpunit h hh

/-- Every positive exponent works when the residue field has characteristic zero. -/
theorem residue_charZero_root [CharZero (ResidueField R)]
    (n : ℕ) (hn : 0 < n) (h : Rˣ) (hh : residue R (h : R) = 1) :
    ∃ y : Rˣ, residue R (y : R) = 1 ∧ y ^ n = h :=
  exists_pow_eq_of_residue_charZero n hn h hh

/-- The zero exponent cannot have a nonidentity principal unit as its power. -/
theorem exponent_zero_obstruction (h : Rˣ) (hh : h ≠ 1) :
    ¬ ∃ y : Rˣ, residue R (y : R) = 1 ∧ y ^ 0 = h := by
  rintro ⟨y, -, hy⟩
  exact hh (by simpa only [pow_zero] using hy.symm)

end ColibTest.HenselianPrincipalRoots
