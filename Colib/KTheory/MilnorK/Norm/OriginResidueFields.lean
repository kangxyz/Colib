/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Polynomial.FactorContraction
public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.ConstantRetraction

/-!
# The actual origin local map and its residue-field dictionary

The coefficient map contracts the target ideal `(X)` to the source ideal `(X)`. Its existing
localization map preserves the literal uniformizer `X`; its native residue-field map agrees
with the coefficient homomorphism through the existing `residueFieldAtOriginEquiv`.

No new local ring, map, residue-field identification, or norm is defined. The source and
target field universes are independent. This source-only draft has not been compiled.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing

universe u v

namespace Polynomial

/-- The coefficient preimage of the actual origin ideal is the source origin ideal. -/
theorem span_X_comap_mapRingHom
    {k : Type u} [Field k] {K : Type v} [Field K] (φ : k →+* K) :
    (Ideal.span ({X} : Set K[X])).comap (Polynomial.mapRingHom φ) =
      Ideal.span ({X} : Set k[X]) :=
  span_singleton_comap_mapRingHom_of_dvd_irreducible_map φ
    (p := X) irreducible_X (q := X) irreducible_X.not_isUnit (by simp)

end Polynomial

namespace Stacks.Chow

variable {k : Type u} [Field k] {K : Type v} [Field K]

/-- The native local coefficient map preserves the specified origin uniformizer exactly.
In particular its ramification exponent is one and its unit correction is one. -/
theorem localRingHom_algebraMap_X (φ : k →+* K) :
    Localization.localRingHom (Ideal.span ({X} : Set k[X]))
        (Ideal.span ({X} : Set K[X])) (Polynomial.mapRingHom φ)
        (Polynomial.span_X_comap_mapRingHom φ).symm
        (algebraMap k[X] (localRingAtOrigin k) X) =
      algebraMap K[X] (localRingAtOrigin K) X := by
  rw [Localization.localRingHom_to_map]
  simp only [Polynomial.coe_mapRingHom, Polynomial.map_X]

/-- The actual map of origin residue fields commutes with their native coefficient-field
identifications. Constants exhaust both residue fields, so no quotient model is required. -/
theorem residueField_map_comp_residueFieldAtOriginEquiv (φ : k →+* K) :
    (IsLocalRing.ResidueField.map
      (Localization.localRingHom (Ideal.span ({X} : Set k[X]))
        (Ideal.span ({X} : Set K[X])) (Polynomial.mapRingHom φ)
        (Polynomial.span_X_comap_mapRingHom φ).symm)).comp
        (residueFieldAtOriginEquiv k).toRingHom =
      (residueFieldAtOriginEquiv K).toRingHom.comp φ := by
  apply RingHom.ext
  intro c
  change IsLocalRing.ResidueField.map
      (Localization.localRingHom (Ideal.span ({X} : Set k[X]))
        (Ideal.span ({X} : Set K[X])) (Polynomial.mapRingHom φ)
        (Polynomial.span_X_comap_mapRingHom φ).symm)
      (residue (localRingAtOrigin k) (algebraMap k[X] (localRingAtOrigin k) (C c))) =
    residue (localRingAtOrigin K) (algebraMap K[X] (localRingAtOrigin K) (C (φ c)))
  rw [IsLocalRing.ResidueField.map_residue, Localization.localRingHom_to_map]
  simp only [Polynomial.coe_mapRingHom, Polynomial.map_C]

/-- Returning through the target origin residue-field equivalence gives exactly the
coefficient map after returning through the source equivalence. -/
theorem residueFieldAtOriginEquiv_symm_comp_residueField_map (φ : k →+* K) :
    (residueFieldAtOriginEquiv K).symm.toRingHom.comp
      (IsLocalRing.ResidueField.map
        (Localization.localRingHom (Ideal.span ({X} : Set k[X]))
          (Ideal.span ({X} : Set K[X])) (Polynomial.mapRingHom φ)
          (Polynomial.span_X_comap_mapRingHom φ).symm)) =
      φ.comp (residueFieldAtOriginEquiv k).symm.toRingHom := by
  apply RingHom.ext
  intro x
  obtain ⟨c, rfl⟩ := (residueFieldAtOriginEquiv k).surjective x
  have h := RingHom.congr_fun (residueField_map_comp_residueFieldAtOriginEquiv φ) c
  change (residueFieldAtOriginEquiv K).symm
      (IsLocalRing.ResidueField.map
        (Localization.localRingHom (Ideal.span ({X} : Set k[X]))
          (Ideal.span ({X} : Set K[X])) (Polynomial.mapRingHom φ)
          (Polynomial.span_X_comap_mapRingHom φ).symm)
        (residueFieldAtOriginEquiv k c)) =
    φ ((residueFieldAtOriginEquiv k).symm (residueFieldAtOriginEquiv k c))
  change IsLocalRing.ResidueField.map _ (residueFieldAtOriginEquiv k c) =
    residueFieldAtOriginEquiv K (φ c) at h
  rw [h, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]

end Stacks.Chow

end
