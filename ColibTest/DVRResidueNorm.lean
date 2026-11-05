/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.Norm.DVRResidue

/-!
# Regressions for DVR residue norms

These consumers retain independent universes, the literal closed fibre, its
extended-natural self-length, the actual integral norm, and both original residue
maps. They do not assume freeness in the DVR section, separability, completeness,
or a characteristic restriction.

Adapted and extended from `AglibTest/DVRNormResidueUnit.lean` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`, SHA-256
`77a205d0c5f1d6da52e5e02ff3e383fa57c60dd80e2c8aeaf74034542c0454bc`.
-/

noncomputable section

open IsLocalRing

universe u v

section LocalAlgebra

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [IsLocalRing R]
  [Algebra R S] [Module.Free R S] [Module.Finite R S]

-- No local-ring or nontriviality assumption on S is needed for base change.
example (b : S) :
    let _ : Algebra (ResidueField R) (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
      Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
    Algebra.norm (ResidueField R)
      (Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R S)) b) =
        residue R (Algebra.norm R b) :=
  Algebra.norm_closedFiber R S b

-- The quotient's own ring supplies the scalars in the exponent's length.
example [IsLocalRing S] [IsLocalHom (algebraMap R S)] (b : S) :
    residue R (Algebra.norm R b) =
      Algebra.norm (ResidueField R) (residue S b) ^
        (Module.length (S ⧸ (maximalIdeal R).map (algebraMap R S))
          (S ⧸ (maximalIdeal R).map (algebraMap R S))).toNat :=
  Algebra.residue_norm_eq_norm_residue_pow_length R S b

end LocalAlgebra

section DVRStructural

variable (R : Type u) (S : Type v) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
  {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)

-- Neither the ideal equation nor the length needs a finite or local algebra map.
example (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e) :
    (maximalIdeal R).map (algebraMap R S) = maximalIdeal S ^ e :=
  IsDiscreteValuationRing.map_maximalIdeal_eq_pow_of_uniformizer R S hπ hϖ u e he

example (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e) :
    Module.length (S ⧸ (maximalIdeal R).map (algebraMap R S))
      (S ⧸ (maximalIdeal R).map (algebraMap R S)) = e :=
  IsDiscreteValuationRing.closedFiber_length_eq_ramification R S hπ hϖ u e he

-- The exponent is proved finite before taking its natural-number value.
example (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e) :
    Module.length (S ⧸ (maximalIdeal R).map (algebraMap R S))
      (S ⧸ (maximalIdeal R).map (algebraMap R S)) ≠ ⊤ := by
  rw [IsDiscreteValuationRing.closedFiber_length_eq_ramification R S hπ hϖ u e he]
  exact ENat.natCast_ne_top e

example (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e) :
    (Module.length (S ⧸ (maximalIdeal R).map (algebraMap R S))
      (S ⧸ (maximalIdeal R).map (algebraMap R S))).toNat = e := by
  rw [IsDiscreteValuationRing.closedFiber_length_eq_ramification R S hπ hϖ u e he,
    ENat.toNat_natCast]

-- The standalone statement covers exponent zero without assuming a local map.
example (u : Sˣ) (he : algebraMap R S π = (u : S) * ϖ ^ 0) :
    Module.length (S ⧸ (maximalIdeal R).map (algebraMap R S))
      (S ⧸ (maximalIdeal R).map (algebraMap R S)) = 0 :=
  IsDiscreteValuationRing.closedFiber_length_eq_ramification R S hπ hϖ u 0 he

end DVRStructural

section DVRIntegral

variable (R : Type u) (S : Type v) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
  [Module.Finite R S] [Module.IsTorsionFree R S] [IsLocalHom (algebraMap R S)]
  {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
  (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e)

include hπ hϖ he

-- The caller supplies finite torsion-freeness, not a selected free basis.
example (b : S) :
    residue R (Algebra.intNorm R S b) =
      Algebra.norm (ResidueField R) (residue S b) ^ e :=
  Algebra.residue_intNorm_eq_norm_residue_pow R S hπ hϖ u e he b

-- The formula includes nonunits and zero.
example :
    residue R (Algebra.intNorm R S (0 : S)) =
      Algebra.norm (ResidueField R) (residue S (0 : S)) ^ e :=
  Algebra.residue_intNorm_eq_norm_residue_pow R S hπ hϖ u e he (0 : S)

example (b : Sˣ) :
    Units.map (residue R).toMonoidHom (Units.map (Algebra.intNorm R S) b) =
      Units.map (Algebra.norm (ResidueField R))
        (Units.map (residue S).toMonoidHom b) ^ e :=
  Algebra.residueUnits_intNorm_eq_norm_pow R S hπ hϖ u e he b

-- Characteristic two is allowed; no separability is introduced here.
example [_residueCharacteristicTwo : CharP (ResidueField R) 2] (b : Sˣ) :
    Units.map (residue R).toMonoidHom (Units.map (Algebra.intNorm R S) b) =
      Units.map (Algebra.norm (ResidueField R))
        (Units.map (residue S).toMonoidHom b) ^ e :=
  Algebra.residueUnits_intNorm_eq_norm_pow R S hπ hϖ u e he b

-- Principal residue-one units remain residue-one under the actual integral norm.
example (b : Sˣ) (hb : Units.map (residue S).toMonoidHom b = 1) :
    Units.map (residue R).toMonoidHom (Units.map (Algebra.intNorm R S) b) = 1 := by
  rw [Algebra.residueUnits_intNorm_eq_norm_pow R S hπ hϖ u e he b, hb, map_one, one_pow]

end DVRIntegral
