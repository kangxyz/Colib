/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.Henselian.UniformizerNormalization

/-! Direct consumers preserve the literal local map, the actual residue-one
root and the normalized uniformizer equation. Invertibility of the exponent
is explicit except where residue characteristic zero genuinely supplies it.

Adapted from `AglibTest/HenselianUniformizerNormalization.lean` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`, SHA-256
`26407334d93c7a5d3c305d78d9aef3f0dd3a0254ae296935a38b1392d715b51f`.
-/

noncomputable section

open IsLocalRing

universe u v

namespace ColibTest.HenselianUniformizerNormalization

variable {R : Type u} {S : Type v} [CommRing R] [IsLocalRing R]
  [CommRing S] [HenselianLocalRing S] (j : R →+* S) [IsLocalHom j]
  (hj : Function.Surjective (ResidueField.map j))

include hj

/-- The lift is a genuine base-ring unit, not merely a residue-field scalar. -/
theorem unit_lift (u : Sˣ) :
    ∃ a : Rˣ, residue S (j (a : R)) = residue S (u : S) :=
  IsLocalRing.exists_unit_residue_lift j hj u

/-- No characteristic assumption is needed for an explicitly invertible exponent. -/
theorem principal_root_factorization (e : ℕ) (he : 0 < e)
    (heunit : IsUnit (e : S)) (u : Sˣ) :
    ∃ (a : Rˣ) (v : Sˣ), residue S (v : S) = 1 ∧
      Units.map j.toMonoidHom a * v ^ e = u :=
  IsLocalRing.exists_base_unit_mul_principal_pow j hj e he heunit u

/-- The exponent-one edge case retains the actual residue-one adjustment. -/
theorem exponent_one {π : R} {ϖ : S} (hϖ : Irreducible ϖ)
    (u : Sˣ) (hπ : j π = (u : S) * ϖ) :
    ∃ (a : Rˣ) (v : Sˣ), residue S (v : S) = 1 ∧
      Irreducible ((v : S) * ϖ) ∧ j π = j (a : R) * ((v : S) * ϖ) := by
  simpa only [pow_one] using IsLocalRing.exists_principal_adjusted_uniformizer
    j hj hϖ u 1 (by decide) (by simp)
    (by simpa only [pow_one] using hπ)

/-- Residue characteristic zero supplies invertibility, rather than being
silently inferred from characteristic zero of a fraction field. -/
theorem residue_characteristic_zero [CharZero (ResidueField S)]
    {π : R} {ϖ : S} (hϖ : Irreducible ϖ) (u : Sˣ) (e : ℕ) (he : 0 < e)
    (hπ : j π = (u : S) * ϖ ^ e) :
    ∃ (a : Rˣ) (v : Sˣ), residue S (v : S) = 1 ∧
      Irreducible ((v : S) * ϖ) ∧ j π = j (a : R) * ((v : S) * ϖ) ^ e :=
  IsLocalRing.exists_principal_adjusted_uniformizer j hj hϖ u e he
    (HenselianLocalRing.PrincipalRoots.isUnit_natCast_of_residue_charZero e he) hπ

omit hj in
/-- The degree-one corollary uses the original residue algebra structure. -/
theorem actual_residue_degree_one [Algebra R S] [IsLocalHom (algebraMap R S)]
    (hf : Module.finrank (ResidueField R) (ResidueField S) = 1)
    {π : R} {ϖ : S} (hϖ : Irreducible ϖ) (u : Sˣ) (e : ℕ) (he : 0 < e)
    (heunit : IsUnit (e : S)) (hπ : algebraMap R S π = (u : S) * ϖ ^ e) :
    ∃ (a : Rˣ) (v : Sˣ), residue S (v : S) = 1 ∧
      Irreducible ((v : S) * ϖ) ∧
      algebraMap R S π = algebraMap R S (a : R) * ((v : S) * ϖ) ^ e :=
  HenselianLocalRing.exists_principal_adjusted_uniformizer_of_residue_finrank_one
    R S hf hϖ u e he heunit hπ

end ColibTest.HenselianUniformizerNormalization
