/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.RingTheory.Length
import Mathlib.RingTheory.LocalRing.Length

/-!
# The length-degree formula over a field

The contribution of a point of a finite scheme over a field is the length of its local ring
times the degree of its residue field. The sum is the dimension of the finite algebra.
See Stacks Project, Tags 02M0 and 02RH.
-/

@[expose] public noncomputable section

namespace IsLocalRing

/-- Over a field the dimension of a finite local algebra is its local length multiplied by
the degree of its residue field. -/
@[colib_tag "COL-0011", stacks 02M0 "field-base local-algebra specialization"]
theorem finrank_eq_length_mul_residueFinrank (k A : Type*) [Field k] [CommRing A]
    [Algebra k A] [IsLocalRing A] [Module.Finite k A] :
    Module.finrank k A = (Module.length A A).toNat * Module.finrank k (ResidueField A) := by
  let : Module.Finite k (ResidueField A) :=
    Module.Finite.of_surjective (IsScalarTower.toAlgHom k A (ResidueField A)).toLinearMap
      (residue_surjective (R := A))
  have h := length_restrictScalars k A A
  rw [← Module.length_eq_of_surjective (M := ResidueField A) (residue_surjective (R := k)),
    Module.length_eq_finrank, Module.length_eq_finrank] at h
  simpa using congrArg ENat.toNat h

end IsLocalRing

namespace IsArtinianRing

/-- The dimension of a finite algebra is the sum of its local lengths weighted by residue
degrees. This gives the affine fibre coefficient in the finite-flat cycle formula. -/
@[colib_tag "COL-0012", stacks 02M0 "finite-algebra length-degree sum over a field",
  stacks 02RH "affine fibre coefficient calculation"]
theorem finrank_eq_finsum_length_mul_residueFinrank (k A : Type*) [Field k] [CommRing A]
    [Algebra k A] [Module.Finite k A] :
    Module.finrank k A = ∑ᶠ x : PrimeSpectrum A,
      (Module.length (Localization.AtPrime x.asIdeal) (Localization.AtPrime x.asIdeal)).toNat *
        Module.finrank k (IsLocalRing.ResidueField (Localization.AtPrime x.asIdeal)) := by
  classical
  let : IsArtinianRing A := isArtinian_of_tower k (M := A) inferInstance
  let := Fintype.ofFinite (PrimeSpectrum A)
  rw [finsum_eq_sum_of_fintype, finrank_eq_sum_primeSpectrum]
  apply Finset.sum_congr rfl
  intro x _
  let R := Localization.AtPrime x.asIdeal
  let : Module.Finite k R :=
    Module.Finite.of_surjective (IsScalarTower.toAlgHom k A R).toLinearMap
      (localization_surjective x.asIdeal.primeCompl R)
  exact IsLocalRing.finrank_eq_length_mul_residueFinrank k R

end IsArtinianRing
