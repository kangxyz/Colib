/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.Koszul.PrincipalExtOne
noncomputable section

open CategoryTheory CategoryTheory.Abelian

universe u w

variable {R : Type u} [CommRing R] [HasExt.{w} (ModuleCat.{u} R)]
  (a : R) (ha : IsSMulRegular R a) (N : ModuleCat.{u} R)

-- Arbitrary coefficients, with no coefficient regularity or finiteness assumptions.
example : (N ⧸ LinearMap.range (LinearMap.lsmul R N a)) ≃ₗ[R]
    Ext (ModuleCat.of R (R ⧸ Ideal.span {a})) N 1 :=
  Koszul.principalExtOneLinearEquiv a ha N

example (x : N) :
    Koszul.principalExtOneLinearEquiv a ha N (Submodule.Quotient.mk x) =
      (ModuleCat.principalShortComplex_shortExact a ha).extClass.comp
        (Ext.mk₀ (ModuleCat.ofHom (LinearMap.toSpanSingleton R N x))) (add_zero 1) := by
  rw [Koszul.principalExtOneLinearEquiv_apply_mk, Koszul.principalExtOneClass_apply]

example {N' : ModuleCat.{u} R} (g : N ⟶ N') (x : N) :
    (Koszul.principalExtOneClass a ha N x).comp (Ext.mk₀ g) (add_zero 1) =
      Koszul.principalExtOneClass a ha N' (g x) :=
  Koszul.principalExtOneClass_comp_mk₀ a ha N g x

-- A unit scalar is allowed; no nonunit or properness condition is introduced.
example : (N ⧸ LinearMap.range (LinearMap.lsmul R N (1 : R))) ≃ₗ[R]
    Ext (ModuleCat.of R (R ⧸ Ideal.span {(1 : R)})) N 1 :=
  Koszul.principalExtOneLinearEquiv 1 (IsSMulRegular.one R) N
