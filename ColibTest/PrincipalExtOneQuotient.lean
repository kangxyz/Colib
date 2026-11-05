/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.Koszul.PrincipalExtOneQuotient

noncomputable section

open CategoryTheory CategoryTheory.Abelian
open scoped Pointwise

universe u w

variable {R : Type u} [CommRing R] [HasExt.{w} (ModuleCat.{u} R)]
  (a : R) (ha : IsSMulRegular R a) (N : ModuleCat.{u} R)

-- The coefficient quotient has its existing Mathlib module instance, with no local replacement.
example : Module (R ⧸ Ideal.span {a}) (N ⧸ (Ideal.span {a} • (⊤ : Submodule R N))) :=
  inferInstance

example :
    letI := Ext.quotientSourceModule (Ideal.span {a}) N 1
    (N ⧸ (Ideal.span {a} • (⊤ : Submodule R N))) ≃ₗ[R ⧸ Ideal.span {a}]
      Ext (ModuleCat.of R (R ⧸ Ideal.span {a})) N 1 :=
  Koszul.principalExtOneQuotientLinearEquiv a ha N

example (x : N) :
    Koszul.principalExtOneQuotientLinearEquiv a ha N (Submodule.Quotient.mk x) =
      (ModuleCat.principalShortComplex_shortExact a ha).extClass.comp
        (Ext.mk₀ (ModuleCat.ofHom (LinearMap.toSpanSingleton R N x))) (add_zero 1) := by
  rw [Koszul.principalExtOneQuotientLinearEquiv_apply_mk, Koszul.principalExtOneClass_apply]

example (b : R ⧸ Ideal.span {a}) (x : N ⧸ (Ideal.span {a} • (⊤ : Submodule R N))) :
    Koszul.principalExtOneQuotientLinearEquiv a ha N (b • x) =
      (Ext.mk₀ (Ext.quotientSourceMul (Ideal.span {a}) b)).comp
        (Koszul.principalExtOneQuotientLinearEquiv a ha N x) (zero_add 1) :=
  Koszul.principalExtOneQuotientLinearEquiv_smul a ha N b x
