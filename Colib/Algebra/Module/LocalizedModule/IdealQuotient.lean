/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Localization of an actual ideal coefficient quotient

The induced map M/IM → N/IN of an actual module localization is again a
localization. This exposes the generic quotient step of
`Aglib.Algebra.Homology.Koszul.Ext.Localization` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`, using Mathlib's localized submodule
and quotient constructions, without introducing another localization model.
-/

@[expose] public noncomputable section

open scoped Pointwise

namespace Submodule

variable {R : Type*} [CommRing R] (T : Submonoid R)
  {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (g : M →ₗ[R] N) [IsLocalizedModule T g]

/-- Quotienting a module localization by ideal multiples retains localization. -/
theorem isLocalizedModule_mapQ_smul_top (I : Ideal R) :
    IsLocalizedModule T (((I • (⊤ : Submodule R M)).mapQ
      (I • (⊤ : Submodule R N)) g
        (Submodule.smul_top_le_comap_smul_top I g))) := by
  let : Module (Localization T) N := IsLocalizedModule.module T g
  let : IsScalarTower R (Localization T) N :=
    IsLocalizedModule.isScalarTower_module T g
  let P : Submodule R M := I • ⊤
  let P' : Submodule (Localization T) N := P.localized' (Localization T) T g
  have hP : P'.restrictScalars R = I • (⊤ : Submodule R N) := by
    dsimp only [P', P]
    rw [Submodule.restrictScalars_localized', Submodule.localized₀_smul,
      Submodule.localized₀_top]
  let e : (N ⧸ P') ≃ₗ[R] N ⧸ (I • (⊤ : Submodule R N)) :=
    (Submodule.Quotient.restrictScalarsEquiv R P').symm.trans
      (Submodule.quotEquivOfEq _ _ hP)
  let q := P.toLocalizedQuotient' (Localization T) T g
  let : IsLocalizedModule T q := by dsimp only [q]; infer_instance
  have heq : (I • (⊤ : Submodule R M)).mapQ
        (I • (⊤ : Submodule R N)) g
        (Submodule.smul_top_le_comap_smul_top I g) = e.toLinearMap.comp q := by
    apply LinearMap.ext
    intro x
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective P x
    change Submodule.Quotient.mk (g m) = e (q (Submodule.Quotient.mk m))
    simp [e, q]
  rw [heq]
  exact IsLocalizedModule.of_linearEquiv T q e

end Submodule
