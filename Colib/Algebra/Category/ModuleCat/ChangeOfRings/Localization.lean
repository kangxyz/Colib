/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# The original scalar-extension adjunction unit at a localization

When the target ring is a localization through the specified ring map,
the native extension/restriction adjunction unit is a module-localization
map. The comparison uses the native tensor product and its existing localization instance.

Adapted from `Aglib/Algebra/Category/ModuleCat/Localization/ScalarExtension.lean`
at revision `101dbb8564fb0e29f28cfcb79168d878b5ab489f`.
The original unit-localization proof is retained with native ownership.
-/

@[expose] public section

noncomputable section


open CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace ModuleCat

universe r s m

variable {R : Type r} {S : Type s} [CommRing R] [CommRing S]
  (T : Submonoid R) (σ : R →+* S)
  (hσ : letI := σ.toAlgebra; IsLocalization T S)

include hσ in
/-- The original native scalar-extension adjunction unit localizes at the specified submonoid. -/
theorem extendRestrictScalarsAdj_unit_isLocalizedModule (M : ModuleCat.{max m s} R) :
    IsLocalizedModule T ((extendRestrictScalarsAdj.{m} σ).unit.app M).hom := by
  let : Algebra R S := σ.toAlgebra
  let : IsLocalization T S := hσ
  let N : ModuleCat.{max m s} R := ModuleCat.of R (S ⊗[R] M)
  let e : N ≅ (restrictScalars σ).obj ((extendScalars σ).obj M) := by
    refine isoMk (AddEquiv.refl _).toAddCommGrpIso ?_
    intro a
    ext x
    change S ⊗[R] M at x
    change σ a • x = a • x
    exact IsScalarTower.algebraMap_smul S a x
  let ℓ : M →ₗ[R] S ⊗[R] M := TensorProduct.mk R S M 1
  let : IsLocalizedModule T ℓ := inferInstance
  have he : ((extendRestrictScalarsAdj.{m} σ).unit.app M).hom =
      e.toLinearEquiv.toLinearMap.comp ℓ := by
    ext x
    rfl
  rw [he]
  exact IsLocalizedModule.of_linearEquiv T ℓ e.toLinearEquiv

end ModuleCat
