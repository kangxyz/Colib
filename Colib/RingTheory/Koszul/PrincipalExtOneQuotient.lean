/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Koszul.PrincipalExtOne
public import Colib.Algebra.Homology.DerivedCategory.Ext.Quotient

/-!
# Quotient-linearity of the principal Ext-one calculation

The coefficient quotient uses Mathlib's existing `R/I`-module structure on
`N/(I • ⊤)`, rather than introducing another quotient-action instance.
Its comparison with the scalar-image quotient preserves every representative.

This is the quotient-linearity endpoint of Aglib's
`Algebra/Homology/Koszul/Single/Ext/Ideal.lean` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`, for the standard connecting-class
normalization of `principalExtOneLinearEquiv`. Comparison of this normalization
with Aglib's old resolution cocycle, including its sign, remains separate.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian
open scoped Pointwise

universe u w

namespace Koszul

variable {R : Type u} [CommRing R] [HasExt.{w} (ModuleCat.{u} R)]
  (a : R) (ha : IsSMulRegular R a) (N : ModuleCat.{u} R)

/-- The principal Ext-one calculation is linear for the native quotient-ring actions. -/
def principalExtOneQuotientLinearEquiv :
    letI := Ext.quotientSourceModule (Ideal.span {a}) N 1
    (N ⧸ (Ideal.span {a} • (⊤ : Submodule R N))) ≃ₗ[R ⧸ Ideal.span {a}]
      Ext (ModuleCat.of R (R ⧸ Ideal.span {a})) N 1 := by
  letI := Ext.quotientSourceModule (Ideal.span {a}) N 1
  let e := (Submodule.quotEquivOfEq (Ideal.span {a} • (⊤ : Submodule R N))
    (LinearMap.range (LinearMap.lsmul R N a)) (by
      rw [Submodule.ideal_span_singleton_smul, Submodule.pointwise_smul_def, Submodule.map_top]
      rfl)).trans
    (principalExtOneLinearEquiv a ha N)
  exact {
    __ := e.toAddEquiv
    map_smul' := by
      intro b x
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
      simp only [RingHom.id_apply]
      rw [Ext.quotientSourceModule_mk_smul]
      change e (r • x) = r • e x
      exact e.map_smul r x }

/-- Quotient-linearity does not change the normalized class of a coefficient representative. -/
@[simp]
theorem principalExtOneQuotientLinearEquiv_apply_mk (x : N) :
    principalExtOneQuotientLinearEquiv a ha N (Submodule.Quotient.mk x) =
      principalExtOneClass a ha N x := by
  change principalExtOneLinearEquiv a ha N
    ((Submodule.quotEquivOfEq (Ideal.span {a} • (⊤ : Submodule R N))
    (LinearMap.range (LinearMap.lsmul R N a)) (by
      rw [Submodule.ideal_span_singleton_smul, Submodule.pointwise_smul_def, Submodule.map_top]
      rfl))
      (Submodule.Quotient.mk x)) = _
  rw [Submodule.quotEquivOfEq_mk, principalExtOneLinearEquiv_apply_mk]

/-- Quotient scalars act by Yoneda precomposition with actual source multiplication. -/
theorem principalExtOneQuotientLinearEquiv_smul (b : R ⧸ Ideal.span {a})
    (x : N ⧸ (Ideal.span {a} • (⊤ : Submodule R N))) :
    principalExtOneQuotientLinearEquiv a ha N (b • x) =
      (Ext.mk₀ (Ext.quotientSourceMul (Ideal.span {a}) b)).comp
        (principalExtOneQuotientLinearEquiv a ha N x) (zero_add 1) := by
  let := Ext.quotientSourceModule (Ideal.span {a}) N 1
  rw [(principalExtOneQuotientLinearEquiv a ha N).map_smul]
  exact Ext.quotientSourceModule_smul_eq_precomp _ _ _ _ _

/-- Coefficient postcomposition preserves the class of every literal representative. -/
theorem principalExtOneQuotientLinearEquiv_comp_mk₀ {N' : ModuleCat.{u} R}
    (g : N ⟶ N') (x : N) :
    (principalExtOneQuotientLinearEquiv a ha N (Submodule.Quotient.mk x)).comp
        (Ext.mk₀ g) (add_zero 1) =
      principalExtOneQuotientLinearEquiv a ha N' (Submodule.Quotient.mk (g x)) := by
  rw [principalExtOneQuotientLinearEquiv_apply_mk, principalExtOneQuotientLinearEquiv_apply_mk,
    principalExtOneClass_comp_mk₀]

end Koszul

attribute [colib_tag "COL-0123"] Koszul.principalExtOneQuotientLinearEquiv
  Koszul.principalExtOneQuotientLinearEquiv_apply_mk
  Koszul.principalExtOneQuotientLinearEquiv_smul
  Koszul.principalExtOneQuotientLinearEquiv_comp_mk₀

attribute [stacks 06XP
  "Ingredient: composition after Lemma 13.27.6; quotient-linearity is derived here"]
  Koszul.principalExtOneQuotientLinearEquiv_smul
