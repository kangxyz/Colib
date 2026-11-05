/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.DiscreteValuationRing.RamificationDegree

/-! Direct actual-data consumers of the ramification-times-residue degree
formula, including the two prime-degree branches and the nonzero exponent.

Adapted from `AglibTest/DVRRamificationDegree.lean` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`, SHA-256
`3d4ee59361ff8ba65d4d2a3094fff786c6214d7ba62b1880ca62050e1c481761`.
-/

noncomputable section

open IsLocalRing

universe u v w z

namespace ColibTest.DVRRamificationDegree

variable (R : Type u) (S : Type v) (F : Type w) (E : Type z)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
  [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
  {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
  (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)

include F E hπ hϖ he

/-- The literal exponent and actual residue degree give the actual field degree. -/
theorem actual_degree :
    Module.finrank F E = e * Module.finrank (ResidueField R) (ResidueField S) :=
  IsDiscreteValuationRing.finrank_eq_ramification_mul_residue_finrank R S F E hπ hϖ u e he

/-- Finite field extensions are nonzero, so the supplied exponent must be positive. -/
theorem exponent_positive [FiniteDimensional F E] : 0 < e := by
  have hd := actual_degree R S F E hπ hϖ u e he
  have hn := Module.finrank_pos (R := F) (M := E)
  rw [hd] at hn
  apply Nat.pos_of_ne_zero
  intro hz
  simp only [hz, zero_mul, lt_self_iff_false] at hn

/-- Prime degree gives exactly the two actual alternatives. -/
theorem prime_dichotomy (hp : Nat.Prime (Module.finrank F E)) :
    e = 1 ∨ Module.finrank (ResidueField R) (ResidueField S) = 1 :=
  IsDiscreteValuationRing.ramification_eq_one_or_residue_finrank_eq_one
    R S F E hπ hϖ u e he hp

/-- In the residue-degree-one branch the literal exponent is the field degree. -/
theorem residue_degree_one
    (hf : Module.finrank (ResidueField R) (ResidueField S) = 1) :
    Module.finrank F E = e := by
  simpa only [hf, mul_one] using actual_degree R S F E hπ hϖ u e he

/-- In the exponent-one branch the residue degree is the field degree. -/
theorem exponent_one (he1 : e = 1) :
    Module.finrank F E = Module.finrank (ResidueField R) (ResidueField S) := by
  simpa only [he1, one_mul] using actual_degree R S F E hπ hϖ u e he

end ColibTest.DVRRamificationDegree
