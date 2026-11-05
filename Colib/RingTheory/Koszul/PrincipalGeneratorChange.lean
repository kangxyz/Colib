/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Koszul.PrincipalExtOne

/-!
# Change of a principal regular generator

For regular `a` and `c * a`, the quotient map `R/(c*a) → R/(a)` pulls the
standard principal connecting class of `x` back to the class of `c • x`.
The multiplier need not be a unit and the ideals need not be equal.

This is the one-generator determinant formula motivating
`ChainComplex.Koszul.topExtClass_generatorChange` in the source module
`Aglib.Algebra.Homology.Koszul.Ext.GeneratorChange`
at revision `101dbb8564fb0e29f28cfcb79168d878b5ab489f`, reproved for the standard
connecting-class normalization through native short-exact-sequence naturality.
No resolution comparison or alternative quotient is constructed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian

universe u w

namespace ModuleCat

variable {R : Type u} [CommRing R] (a c : R)

/-- The actual quotient map associated to the inclusion `(c*a) ⊆ (a)`. -/
def principalQuotientMulMap :
    ModuleCat.of R (R ⧸ Ideal.span {c * a}) ⟶ ModuleCat.of R (R ⧸ Ideal.span {a}) :=
  ModuleCat.ofHom ((Ideal.span {c * a}).mapQ (Ideal.span {a}) LinearMap.id (by
    change Ideal.span {c * a} ≤ Ideal.span {a}
    apply Ideal.span_le.mpr
    rintro r (rfl : r = c * a)
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton a))))

/-- Multiplication of the generator gives the native morphism of principal presentations. -/
def principalShortComplexMulHom : principalShortComplex (c * a) ⟶ principalShortComplex a where
  τ₁ := ModuleCat.ofHom (LinearMap.lsmul R R c)
  τ₂ := 𝟙 _
  τ₃ := principalQuotientMulMap a c
  comm₁₂ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change a * (c * r) = (c * a) * r
    ring
  comm₂₃ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    rfl

end ModuleCat

namespace Koszul

variable {R : Type u} [CommRing R] [HasExt.{w} (ModuleCat.{u} R)]

/-- Pullback along `R/(c*a) → R/(a)` multiplies the principal coefficient by `c`. -/
theorem principalExtOneClass_generatorChange (a c : R) (ha : IsSMulRegular R a)
    (hca : IsSMulRegular R (c * a)) (N : ModuleCat.{u} R) (x : N) :
    (Ext.mk₀ (ModuleCat.principalQuotientMulMap a c)).comp
      (principalExtOneClass a ha N x) (zero_add 1) =
        principalExtOneClass (c * a) hca N (c • x) := by
  have hn := (ModuleCat.principalShortComplex_shortExact (c * a) hca).extClass_naturality
    (ModuleCat.principalShortComplex_shortExact a ha) (ModuleCat.principalShortComplexMulHom a c)
  have hn' := congrArg
    (fun z => z.comp (Ext.mk₀ (ModuleCat.ofHom (LinearMap.toSpanSingleton R N x)))
      (add_zero 1)) hn
  change ((ModuleCat.principalShortComplex_shortExact (c * a) hca).extClass.comp
      (Ext.mk₀ (ModuleCat.ofHom (LinearMap.lsmul R R c))) (add_zero 1)).comp
      (Ext.mk₀ (ModuleCat.ofHom (LinearMap.toSpanSingleton R N x))) (add_zero 1) =
    ((Ext.mk₀ (ModuleCat.principalQuotientMulMap a c)).comp
      (ModuleCat.principalShortComplex_shortExact a ha).extClass (zero_add 1)).comp
      (Ext.mk₀ (ModuleCat.ofHom (LinearMap.toSpanSingleton R N x))) (add_zero 1) at hn'
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
    Ext.comp_assoc_of_third_deg_zero] at hn'
  have hc : ModuleCat.ofHom (LinearMap.lsmul R R c) ≫
      ModuleCat.ofHom (LinearMap.toSpanSingleton R N x) =
        ModuleCat.ofHom (LinearMap.toSpanSingleton R N (c • x)) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change (c * r) • x = r • (c • x)
    rw [smul_smul, mul_comm]
  rw [hc] at hn'
  exact hn'.symm

end Koszul

attribute [colib_tag "COL-0110"] Koszul.principalExtOneClass_generatorChange

attribute [stacks 06XP "Ingredient: extension classes; explicit generator change proved here"]
  Koszul.principalExtOneClass_generatorChange
