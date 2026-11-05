/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Koszul.PrincipalGeneratorTransport
public import StacksFrontier.RingTheory.Koszul.TorComparison.QuotientTor

/-!
# The generator from the native singleton Koszul resolution

The degree-one coordinate of Stacks' exterior-power Koszul complex represents
minus the standard connecting class, after the explicit identification of its
quotient with the principal ideal quotient. We use the existing resolution,
augmentation and exterior-power coordinates, without another complex model.

This realizes the generator calculation motivating
`Aglib.Algebra.Homology.Koszul.Single.Ext.Ideal` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f` in the chosen native model.
It does not assert an equality with an imported Aglib declaration.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian

universe u w

namespace Koszul

variable {R : Type u} [CommRing R] (a : R)

/-- The quotient identification for the constant singleton sequence. -/
def singletonSeqQuotientIso :
    ModuleCat.of R (R ⧸ Ideal.span (Set.range (fun _ : Fin 1 => a))) ≅
      ModuleCat.of R (R ⧸ Ideal.span {a}) :=
  (Submodule.quotEquivOfEq _ _ (by simp)).toModuleIso

/-- Degree one in the singleton Koszul complex has its canonical scalar coordinate. -/
def singletonSeqCoordinate :
    (seqComplex (fun _ : Fin 1 => a)).X 1 ⟶ ModuleCat.of R R :=
  ModuleCat.ofHom ((LinearMap.proj 0).comp
    (exteriorPower.oneEquiv R (Fin 1 → R)).toLinearMap)

/-- The coordinate is a cocycle because the singleton complex vanishes in degree two. -/
theorem singletonSeqCoordinate_cocycle :
    (seqComplex (fun _ : Fin 1 => a)).d 2 1 ≫ singletonSeqCoordinate a = 0 :=
  (seqComplex_isZero_of_lt (fun _ : Fin 1 => a) 2 (by decide)).eq_of_src _ _

/-- The degree-one differential is multiplication by the singleton scalar. -/
theorem singletonSeqCoordinate_comp_lsmul :
    singletonSeqCoordinate a ≫ ModuleCat.ofHom (LinearMap.lsmul R R a) =
      (seqComplex (fun _ : Fin 1 => a)).d 1 0 ≫
        (exteriorPower.zeroEquiv R (Fin 1 → R)).toModuleIso.hom := by
  apply ModuleCat.hom_ext
  ext x
  change (⋀[R]^1 (Fin 1 → R)) at x
  change a • ((exteriorPower.oneEquiv R (Fin 1 → R)) x) 0 =
    exteriorPower.zeroEquiv R (Fin 1 → R) (d (seqDual (fun _ : Fin 1 => a)) 0 x)
  rw [zeroEquiv_d_zero, seqDual_apply]
  simp [mul_comm]

/-- The native augmentation agrees with the principal quotient map in degree zero. -/
theorem singletonSeqAugmentation_comp_quotientIso :
    (koszulAugmentation (fun _ : Fin 1 => a)).f 0 ≫ (singletonSeqQuotientIso a).hom =
      (exteriorPower.zeroEquiv R (Fin 1 → R)).toModuleIso.hom ≫
        ModuleCat.ofHom (Ideal.span {a}).mkQ := by
  rw [koszulAugmentation_f_zero]
  apply ModuleCat.hom_ext
  ext x
  rfl

variable [HasExt.{w} (ModuleCat.{u} R)]

/-- The coordinate cocycle of the native singleton resolution gives minus the connecting class. -/
theorem singletonSeqExtMk_eq_neg_class (ha : IsSMulRegular R a)
    (hf : IsKoszulRegular (fun _ : Fin 1 => a)) (N : ModuleCat.{u} R) (x : N) :
    (Ext.mk₀ (singletonSeqQuotientIso a).inv).comp
      ((seqProjectiveResolution (fun _ : Fin 1 => a) hf).extMk
        (singletonSeqCoordinate a ≫ ModuleCat.ofHom (LinearMap.toSpanSingleton R N x))
        2 rfl (by simp [reassoc_of% singletonSeqCoordinate_cocycle]; rfl)) (zero_add 1) =
      -principalExtOneClass a ha N x := by
  apply principalExtMk_transport_eq_neg_class a ha
    (seqProjectiveResolution (fun _ : Fin 1 => a) hf) (singletonSeqQuotientIso a)
    (exteriorPower.zeroEquiv R (Fin 1 → R)).toModuleIso.hom (singletonSeqCoordinate a)
    (singletonSeqCoordinate_cocycle a) (singletonSeqCoordinate_comp_lsmul a)
    (singletonSeqAugmentation_comp_quotientIso a).symm

end Koszul

attribute [colib_tag "COL-0117"] Koszul.singletonSeqExtMk_eq_neg_class

attribute [stacks 06XP "Ingredient: extension classes; the native resolution sign is proved here"]
  Koszul.singletonSeqExtMk_eq_neg_class
