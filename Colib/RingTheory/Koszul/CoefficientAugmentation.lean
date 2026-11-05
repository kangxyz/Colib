/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.Util.References
public import StacksFrontier.RingTheory.Koszul.Augmentation
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.Algebra.Module.ULift

/-!
# The original Koszul augmentation with coefficients

The native exterior Koszul complex with coefficients augments to the actual
coefficient quotient. Its degree-zero homology is that quotient for every
sequence. Koszul regularity on the coefficient makes this same map a
quasi-isomorphism. No flatness of the coefficients or regularity on the ring
is required. The coefficient universe is independent of the ring universe.
The categorical target uses the standard `ULift` to the universe of the
tensor complex; the quotient linear equivalence has the original target.

This extends the ring-coefficient augmentation of the pinned Stacks library,
using Mathlib's right-exact tensor quotient comparison. It completes the
coefficient endpoint suggested by `Aglib.Algebra.Homology.Koszul.Resolution`
at revision `101dbb8564fb0e29f28cfcb79168d878b5ab489f`; it is a new native
extension, not a claim of verbatim correspondence with an unopened archive.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ExteriorAlgebra

universe u v

namespace Koszul

variable {R : Type u} [CommRing R] {r : ℕ}

/-- The literal degree-zero differential quotient with coefficients. -/
abbrev CoefficientHomologyZeroQuotient (f : Fin r → R) (M : ModuleCat.{v} R) :=
  (seqComplexTensor f M).X 0 ⧸ LinearMap.range ((seqComplexTensor f M).d 1 0).hom

/-- Tensor right exactness identifies the original differential quotient with
 the quotient of the coefficients by the generated ideal. -/
noncomputable def coefficientHomologyZeroQuotientEquiv (f : Fin r → R)
    (M : ModuleCat.{v} R) :
    CoefficientHomologyZeroQuotient f M ≃ₗ[R]
      M ⧸ (Ideal.span (Set.range f) • (⊤ : Submodule R M)) := by
  let D := d (seqDual f) 0
  let e : ((⋀[R]^0 (Fin r → R)) ⧸ LinearMap.range D) ≃ₗ[R]
      R ⧸ Ideal.span (Set.range f) :=
    Submodule.Quotient.equiv _ _ (exteriorPower.zeroEquiv R (Fin r → R))
      (range_d_zero f)
  exact (Submodule.quotEquivOfEq _ _ (LinearMap.rTensor_range (g := D) M)).trans
    ((TensorProduct.quotientTensorEquiv M (LinearMap.range D)).symm.trans
      ((e.rTensor M).trans (TensorProduct.quotTensorEquivQuotSMul M _)))

/-- On a pure tensor, the homology quotient map is the ordinary scalar quotient map. -/
@[simp]
theorem coefficientHomologyZeroQuotientEquiv_mk_tmul (f : Fin r → R)
    (M : ModuleCat.{v} R) (x : ⋀[R]^0 (Fin r → R)) (m : M) :
    coefficientHomologyZeroQuotientEquiv f M
        (Submodule.Quotient.mk (x ⊗ₜ[R] m)) =
      Submodule.Quotient.mk ((exteriorPower.zeroEquiv R (Fin r → R)) x • m) := by
  change TensorProduct.quotTensorEquivQuotSMul M (Ideal.span (Set.range f))
    (Ideal.Quotient.mk _ ((exteriorPower.zeroEquiv R (Fin r → R)) x) ⊗ₜ[R] m) = _
  exact TensorProduct.quotTensorEquivQuotSMul_mk_tmul _ _ _

/-- Degree-zero homology is the genuine coefficient quotient, lifted only to match
the universe of the tensor complex. -/
noncomputable def coefficientHomologyZeroIso (f : Fin r → R) (M : ModuleCat.{v} R) :
    (seqComplexTensor f M).homology 0 ≅
      ModuleCat.of R (ULift.{u} (M ⧸ (Ideal.span (Set.range f) • (⊤ : Submodule R M)))) :=
  (seqComplexTensor f M).isoHomologyι₀ ≪≫
    (seqComplexTensor f M).opcyclesIsoSc' 1 0 0 (by simp) (by simp) ≪≫
    ((seqComplexTensor f M).sc' 1 0 0).moduleCatOpcyclesIso ≪≫
    ((coefficientHomologyZeroQuotientEquiv f M).trans ULift.moduleEquiv.symm).toModuleIso

/-- The literal differential-range quotient projection. -/
noncomputable def coefficientQuotientAugmentationMap (f : Fin r → R)
    (M : ModuleCat.{v} R) :
    (seqComplexTensor f M).X 0 ⟶ ModuleCat.of R (CoefficientHomologyZeroQuotient f M) :=
  ModuleCat.ofHom (LinearMap.range ((seqComplexTensor f M).d 1 0).hom).mkQ

@[reassoc]
theorem d_coefficientQuotientAugmentationMap (f : Fin r → R) (M : ModuleCat.{v} R) :
    (seqComplexTensor f M).d 1 0 ≫ coefficientQuotientAugmentationMap f M = 0 :=
  ModuleCat.hom_ext
    (LinearMap.exact_map_mkQ_range ((seqComplexTensor f M).d 1 0).hom).linearMap_comp_eq_zero

/-- The chain augmentation to the literal differential quotient. -/
noncomputable def coefficientQuotientAugmentation (f : Fin r → R) (M : ModuleCat.{v} R) :
    seqComplexTensor f M ⟶ (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj
      (ModuleCat.of R (CoefficientHomologyZeroQuotient f M)) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨coefficientQuotientAugmentationMap f M, d_coefficientQuotientAugmentationMap f M⟩

/-- The literal augmentation computes degree zero without regularity. -/
theorem coefficientQuotientAugmentation_quasiIsoAt_zero
    (f : Fin r → R) (M : ModuleCat.{v} R) :
    QuasiIsoAt (coefficientQuotientAugmentation f M) 0 := by
  rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
  · constructor
    · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
      exact LinearMap.exact_map_mkQ_range ((seqComplexTensor f M).d 1 0).hom
    · exact (ModuleCat.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _)
  · exact (seqComplexTensor f M).shape _ _ (by simp)
  · rfl
  · rfl

/-- The original augmentation with values in the actual coefficient quotient. -/
noncomputable def coefficientAugmentation (f : Fin r → R) (M : ModuleCat.{v} R) :
    seqComplexTensor f M ⟶ (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj
      (ModuleCat.of R (ULift.{u} (M ⧸ (Ideal.span (Set.range f) • (⊤ : Submodule R M))))) :=
  coefficientQuotientAugmentation f M ≫
    (ChainComplex.single₀ (ModuleCat.{max u v} R)).map
      ((coefficientHomologyZeroQuotientEquiv f M).trans ULift.moduleEquiv.symm).toModuleIso.hom

/-- The original augmentation sends a degree-zero pure tensor to its scalar quotient class. -/
theorem coefficientAugmentation_f_zero_tmul (f : Fin r → R) (M : ModuleCat.{v} R)
    (x : ⋀[R]^0 (Fin r → R)) (m : M) :
    ((coefficientAugmentation f M).f 0 (x ⊗ₜ[R] m)).down =
      Submodule.Quotient.mk ((exteriorPower.zeroEquiv R (Fin r → R)) x • m) :=
  coefficientHomologyZeroQuotientEquiv_mk_tmul f M x m

/-- The actual coefficient quotient augmentation always computes degree zero. -/
theorem coefficientAugmentation_quasiIsoAt_zero (f : Fin r → R) (M : ModuleCat.{v} R) :
    QuasiIsoAt (coefficientAugmentation f M) 0 := by
  have := coefficientQuotientAugmentation_quasiIsoAt_zero f M
  unfold coefficientAugmentation
  infer_instance

/-- Koszul regularity on the coefficients makes the original augmentation a quasi-isomorphism. -/
theorem coefficientAugmentation_quasiIso (f : Fin r → R) (M : ModuleCat.{v} R)
    (hf : IsKoszulRegularOn f M) : QuasiIso (coefficientAugmentation f M) := by
  constructor
  intro n
  cases n with
  | zero => exact coefficientAugmentation_quasiIsoAt_zero f M
  | succ n =>
    let L := (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj
      (ModuleCat.of R (ULift.{u} (M ⧸ (Ideal.span (Set.range f) • (⊤ : Submodule R M)))))
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact (hf _ (Nat.succ_ne_zero n)).isIso
      ((L.sc (n + 1)).isZero_homology_of_isZero_X₂
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0
          (ModuleCat.of R (ULift.{u} (M ⧸ (Ideal.span (Set.range f) • (⊤ : Submodule R M)))))
          (n + 1) (by omega))) _

/-- Weak regularity on the coefficients suffices; the ring sequence need not be regular. -/
theorem coefficientAugmentation_quasiIso_of_weaklyRegular
    (f : Fin r → R) (M : ModuleCat.{v} R)
    (hf : RingTheory.Sequence.IsWeaklyRegular M (List.ofFn f)) :
    QuasiIso (coefficientAugmentation f M) :=
  coefficientAugmentation_quasiIso f M
    (isKoszulRegularOn_and_isKoszulRegular_of_regular.1 hf)

end Koszul

attribute [colib_tag "COL-0163",
  colib_ref "axiom_stacks" "RingTheory/Koszul/Augmentation.lean" "adaptation"
    "Extension of the native ring-coefficient augmentation to arbitrary coefficient universes"]
  Koszul.coefficientHomologyZeroQuotientEquiv
  Koszul.coefficientHomologyZeroIso
  Koszul.coefficientAugmentation
  Koszul.coefficientAugmentation_quasiIso
