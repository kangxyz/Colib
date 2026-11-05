/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Koszul.PrincipalSeqGenerator
public import Colib.RingTheory.Koszul.PrincipalGeneratorChange

/-!
# Generator change for the native singleton Koszul resolution

The actual coordinate cocycles of Stacks' `seqProjectiveResolution` transform
by the multiplier when the singleton generator changes from `a` to `c * a`.
The quotient map is explicitly conjugated by the native singleton quotient
identifications. Its action on quotient representatives is the identity.

This specializes the determinant formula of
`ChainComplex.Koszul.topExtClass_generatorChange` in source module
`Aglib.Algebra.Homology.Koszul.Ext.GeneratorChange` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f` to the chosen Stacks model.
The theorem uses the proved negative connecting-class normalization on both
sides, so the signs cancel. A theorem naming the old Aglib class remains separate.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian

universe u w

namespace Koszul

variable {R : Type u} [CommRing R] [HasExt.{w} (ModuleCat.{u} R)]

/-- Generator change acts on the actual native singleton resolution cocycles by the multiplier. -/
theorem singletonSeqExtMk_generatorChange (a c : R) (ha : IsSMulRegular R a)
    (hca : IsSMulRegular R (c * a))
    (hf : IsKoszulRegular (fun _ : Fin 1 => a))
    (hcf : IsKoszulRegular (fun _ : Fin 1 => c * a)) (N : ModuleCat.{u} R) (x : N) :
    (Ext.mk₀ ((singletonSeqQuotientIso (c * a)).hom ≫
      ModuleCat.principalQuotientMulMap a c ≫ (singletonSeqQuotientIso a).inv)).comp
      ((seqProjectiveResolution (fun _ : Fin 1 => a) hf).extMk
        (singletonSeqCoordinate a ≫ ModuleCat.ofHom (LinearMap.toSpanSingleton R N x))
        2 rfl (by simp [reassoc_of% singletonSeqCoordinate_cocycle]; rfl)) (zero_add 1) =
      (seqProjectiveResolution (fun _ : Fin 1 => c * a) hcf).extMk
        (singletonSeqCoordinate (c * a) ≫
          ModuleCat.ofHom (LinearMap.toSpanSingleton R N (c • x)))
        2 rfl (by simp [reassoc_of% singletonSeqCoordinate_cocycle]; rfl) := by
  have hinj : Function.Injective (fun z : Ext
      (ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun _ : Fin 1 => c * a)))) N 1 =>
        (Ext.mk₀ (singletonSeqQuotientIso (c * a)).inv).comp z (zero_add 1)) := by
    intro y z h
    have h' := congrArg (fun t =>
      (Ext.mk₀ (singletonSeqQuotientIso (c * a)).hom).comp t (zero_add 1)) h
    simpa only [Ext.mk₀_comp_mk₀_assoc, Iso.hom_inv_id, Ext.mk₀_id_comp] using h'
  apply hinj
  dsimp only
  erw [Ext.mk₀_comp_mk₀_assoc]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  erw [← Ext.mk₀_comp_mk₀_assoc, singletonSeqExtMk_eq_neg_class a ha hf,
    singletonSeqExtMk_eq_neg_class (c * a) hca hcf, Ext.comp_neg,
    principalExtOneClass_generatorChange a c ha hca]

end Koszul

attribute [colib_tag "COL-0114"] Koszul.singletonSeqExtMk_generatorChange

attribute [stacks 06XP "Ingredient: extension classes; explicit generator change proved here"]
  Koszul.singletonSeqExtMk_generatorChange
