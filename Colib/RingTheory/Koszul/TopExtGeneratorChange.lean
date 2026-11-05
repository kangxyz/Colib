/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Koszul.TopExtClass
public import StacksFrontier.RingTheory.Koszul.Functoriality

/-!
# Determinant change of native top Koszul Ext classes

An arbitrary square matrix gives the actual exterior-power chain map
`K(M f) → K(f)`. If both sequences are Koszul-regular, it is a morphism of
the existing projective resolutions over the literal quotient map.
Its top coordinate is multiplication by `det M`, hence so is its action on
native top Ext classes. Neither invertibility nor equality of ideals is needed.

This realizes the determinant formula of
`ChainComplex.Koszul.topExtClass_generatorChange` in
`Aglib.Algebra.Homology.Koszul.Ext.GeneratorChange` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`, using only the selected Stacks model.
The arbitrary-matrix chain construction adapts the proof of Stacks'
`Koszul.seqComplex_mulVec_iso`, retaining its transpose convention, but does
not require the inverse used to construct that isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian

universe u w

namespace Koszul

variable {R : Type u} [CommRing R] {n : ℕ} (f : Fin n → R)
  (M : Matrix (Fin n) (Fin n) R)

/-- The transposed matrix intertwines the two Koszul linear functionals. -/
theorem seqDual_comp_transpose :
    (seqDual f).comp (Matrix.toLin' M.transpose) = seqDual (M.mulVec f) := by
  apply LinearMap.ext
  intro v
  change seqDual f (M.transpose.mulVec v) = seqDual (M.mulVec f) v
  simp only [seqDual_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1 with i
  congr 1 with j
  ac_rfl

/-- An arbitrary square matrix induces a map of the native Koszul complexes. -/
def seqComplexMatrixMap : seqComplex (M.mulVec f) ⟶ seqComplex f where
  f i := ModuleCat.ofHom (exteriorPower.map i (Matrix.toLin' M.transpose))
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    rw [seqComplex_d, seqComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change (⋀[R]^(j + 1) (Fin n → R)) at z
    change d (seqDual f) j (exteriorPower.map (j + 1) (Matrix.toLin' M.transpose) z) =
      exteriorPower.map j (Matrix.toLin' M.transpose) (d (seqDual (M.mulVec f)) j z)
    apply Subtype.ext
    simp only [exteriorPower.coe_map, d_apply_coe]
    exact (koszul_map_comm _ _ _ (seqDual_comp_transpose f M)
      (z : ExteriorAlgebra R (Fin n → R))).symm

/-- Matrix combinations of a sequence generate a subideal of its generated ideal. -/
theorem span_mulVec_le : Ideal.span (Set.range (M.mulVec f)) ≤ Ideal.span (Set.range f) := by
  apply Ideal.span_le.mpr
  rintro x ⟨i, rfl⟩
  change ∑ j, M i j * f j ∈ Ideal.span (Set.range f)
  exact Submodule.sum_mem _ fun j _ =>
    Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)

/-- The literal quotient map induced by the ideal inclusion for matrix combinations. -/
def seqQuotientMatrixMap :
    ModuleCat.of R (R ⧸ Ideal.span (Set.range (M.mulVec f))) ⟶
      ModuleCat.of R (R ⧸ Ideal.span (Set.range f)) :=
  ModuleCat.ofHom ((Ideal.span (Set.range (M.mulVec f))).mapQ
    (Ideal.span (Set.range f)) LinearMap.id (span_mulVec_le f M))

/-- The matrix chain map commutes with the actual Koszul augmentations in degree zero. -/
theorem seqComplexMatrixMap_comp_augmentation :
    (seqComplexMatrixMap f M).f 0 ≫ (koszulAugmentation f).f 0 =
      (koszulAugmentation (M.mulVec f)).f 0 ≫ seqQuotientMatrixMap f M := by
  rw [koszulAugmentation_f_zero, koszulAugmentation_f_zero]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (⋀[R]^0 (Fin n → R)) at z
  change (Ideal.span (Set.range f)).mkQ
      (exteriorPower.zeroEquiv R (Fin n → R)
        (exteriorPower.map 0 (Matrix.toLin' M.transpose) z)) =
    (Ideal.span (Set.range f)).mkQ (exteriorPower.zeroEquiv R (Fin n → R) z)
  exact congrArg (Ideal.span (Set.range f)).mkQ
    (LinearMap.congr_fun (exteriorPower.zeroEquiv_naturality (Matrix.toLin' M.transpose)) z)

/-- The existing native Koszul resolutions are related by the actual matrix chain map. -/
def seqProjectiveResolutionMatrixHom (hf : IsKoszulRegular f)
    (hMf : IsKoszulRegular (M.mulVec f)) :
    ProjectiveResolution.Hom (seqProjectiveResolution (M.mulVec f) hMf)
      (seqProjectiveResolution f hf) (seqQuotientMatrixMap f M) where
  hom := seqComplexMatrixMap f M
  hom_f_zero_comp_π_f_zero := seqComplexMatrixMap_comp_augmentation f M

/-- The matrix chain map acts on the standard ordered top coordinate by its determinant. -/
theorem seqComplexMatrixMap_top :
    (seqComplexMatrixMap f M).f n ≫ (topEquiv R n).toModuleIso.hom =
      (topEquiv R n).toModuleIso.hom ≫ ModuleCat.ofHom (LinearMap.lsmul R R M.det) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (⋀[R]^n (Fin n → R)) at z
  change topEquiv R n (exteriorPower.map n (Matrix.toLin' M.transpose) z) =
    M.det • topEquiv R n z
  rw [exteriorPower.map_top_pi_eq_det_smul, map_smul, Matrix.det_transpose]

/-- An arbitrary matrix changes native top Koszul Ext classes by its determinant. -/
theorem seqTopExtClass_generatorChange [HasExt.{w} (ModuleCat.{u} R)]
    (hf : IsKoszulRegular f) (hMf : IsKoszulRegular (M.mulVec f))
    (N : ModuleCat.{u} R) (x : N) :
    (Ext.mk₀ (seqQuotientMatrixMap f M)).comp (seqTopExtClass f hf N x) (zero_add n) =
      seqTopExtClass (M.mulVec f) hMf N (M.det • x) :=
  seqTopExtClass_covariance f hf (M.mulVec f) hMf (seqQuotientMatrixMap f M)
    (seqProjectiveResolutionMatrixHom f M hf hMf) M.det (seqComplexMatrixMap_top f M) N x

end Koszul

attribute [colib_tag "COL-0112"] Koszul.seqComplexMatrixMap
  Koszul.seqQuotientMatrixMap Koszul.seqComplexMatrixMap_comp_augmentation
  Koszul.seqProjectiveResolutionMatrixHom Koszul.seqComplexMatrixMap_top
  Koszul.seqTopExtClass_generatorChange

attribute [stacks 06XP "Ingredient: Yoneda composition; matrix and determinant formula proved here"]
  Koszul.seqTopExtClass_generatorChange
