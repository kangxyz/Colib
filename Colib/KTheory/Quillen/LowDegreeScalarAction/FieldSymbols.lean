/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Quillen.LowDegreeScalarAction.ScalarUnit
public import Colib.KTheory.Quillen.Field.ModuleDeterminant

/-!
# Positive unit products on the original upper field K-groups

The inverse of the original finite-module determinant supplies the positive
rank-one K1 class. Applying the original scalar identity-homotopy action defines
the ordered product. Both multiplicative laws and field-extension naturality
concern the literal upper SmallK objects and original tensor maps. The separate
positive-symbol marking compares this product with the canonical Milnor map.
-/
/-! Implementation source: `Quillen/KTheory/LowDegreeScalarAction/FieldSymbols.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original normalized-Q maps,
whole identity tracks, upper SmallK and tensor-extension formulas are retained.
Unused degree-zero and optional matrix-cube calibrations are not imported. -/
@[expose] public section

noncomputable section
open Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.Linear
attribute [local instance] Abelian.hasFiniteBiproducts
open scoped ZeroObject TensorProduct ChangeOfRings

namespace FGModuleCat.FieldSymbols

variable (F : Type u) [Field F]

/-- The original upper K1 class with determinant equal to the prescribed unit. -/
def positiveUnitKOne : Fˣ →*
    (abelianExactStructure (FGModuleCat.{u} F)).SmallK.{u + 1} 1 :=
  (FGModuleCat.moduleDetEquiv F).symm.toMonoidHom

/-- The original scalar operation applied to the positive rank-one K1 class.
Its bilinearity and field naturality are proved below; identification with
the original ordered Milnor symbol is a separate marking theorem. -/
def unitProduct (a b : Fˣ) :
    (abelianExactStructure (FGModuleCat.{u} F)).SmallK.{u + 1} 2 :=
  ScalarUnit.upperFiniteModuleKOneAction F a (positiveUnitKOne F b)

/-- Multiplication in the first unit gives the original K2 product. -/
theorem unitProduct_mul_left (a b c : Fˣ) :
    unitProduct F (a * b) c = unitProduct F a c * unitProduct F b c :=
  DFunLike.congr_fun (ScalarUnit.upperFiniteModuleKOneAction F |>.map_mul a b)
    (positiveUnitKOne F c)

/-- Multiplication in the second unit gives the original K2 product. -/
theorem unitProduct_mul_right (a b c : Fˣ) :
    unitProduct F a (b * c) = unitProduct F a b * unitProduct F a c := by
  unfold unitProduct
  rw [map_mul, map_mul]

/-- The identity in the first unit gives the identity class. -/
@[simp] theorem unitProduct_one_left (b : Fˣ) : unitProduct F 1 b = 1 :=
  DFunLike.congr_fun (ScalarUnit.upperFiniteModuleKOneAction F).map_one
    (positiveUnitKOne F b)

/-- The identity in the second unit gives the identity class. -/
@[simp] theorem unitProduct_one_right (a : Fˣ) : unitProduct F a 1 = 1 := by
  unfold unitProduct
  rw [map_one, map_one]

variable {F} {L : Type u} [Field L] (f : F →+* L)

/-- Actual tensor extension carries the positive rank-one class to the same
positive class with the mapped scalar unit. -/
theorem positiveUnitKOne_natural (b : Fˣ) :
    (FGModuleCat.finiteModuleExtensionExact f).smallKMap.{u + 1} 1 (positiveUnitKOne F b) =
      positiveUnitKOne L (Units.map f.toMonoidHom b) := by
  apply (FGModuleCat.moduleDetEquiv L).injective
  rw [FGModuleCat.moduleDetEquiv_scalarExtension]
  change (Units.map f.toMonoidHom)
      ((FGModuleCat.moduleDetEquiv F) ((FGModuleCat.moduleDetEquiv F).symm b)) =
    (FGModuleCat.moduleDetEquiv L)
      ((FGModuleCat.moduleDetEquiv L).symm ((Units.map f.toMonoidHom) b))
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

private theorem extension_scalar (a : Fˣ) (M : FGModuleCat.{u} F) :
    (FGModuleCat.finiteModuleExtension f).map ((scalarNatAut F (FGModuleCat.{u} F) a).hom.app M) =
      (scalarNatAut L (FGModuleCat.{u} L) (Units.map f.toMonoidHom a)).hom.app
        ((FGModuleCat.finiteModuleExtension f).obj M) := by
  apply ObjectProperty.hom_ext
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  change (1 : L) ⊗ₜ[F, f] ((a : F) • m) =
    (f (a : F)) • ((1 : L) ⊗ₜ[F, f] m)
  let := f.toAlgebra
  change (1 : L) ⊗ₜ[F] ((a : F) • m) =
    (f (a : F)) • ((1 : L) ⊗ₜ[F] m)
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  rfl

private theorem extension_small_scalar (a : Fˣ) (X : SmallModel.{u + 1} (FGModuleCat.{u} F)) :
    (FGModuleCat.finiteModuleExtensionExact f).smallModel.{u + 1}.toFunctor.map
        ((smallModelScalarNatAut.{u, u + 1, u, u + 1} F
          (FGModuleCat.{u} F) a).hom.app X) =
      (smallModelScalarNatAut.{u, u + 1, u, u + 1} L (FGModuleCat.{u} L)
        (Units.map f.toMonoidHom a)).hom.app
        ((FGModuleCat.finiteModuleExtensionExact f).smallModel.{u + 1}.toFunctor.obj X) := by
  change (equivSmallModel.{u + 1} (FGModuleCat.{u} L)).functor.map
    ((FGModuleCat.finiteModuleExtension f).map
      ((equivSmallModel.{u + 1} (FGModuleCat.{u} F)).inverse.map
        ((smallModelScalarNatAut.{u, u + 1, u, u + 1} F (FGModuleCat.{u} F) a).hom.app X))) = _
  rw [smallModelScalarNatAut_map_hom]
  change (equivSmallModel.{u + 1} (FGModuleCat.{u} L)).functor.map
    ((FGModuleCat.finiteModuleExtension f).map
      ((scalarNatAut F (FGModuleCat.{u} F) a).hom.app
        ((equivSmallModel.{u + 1} (FGModuleCat.{u} F)).inverse.obj X))) = _
  rw [extension_scalar]
  exact smallModelScalarNatAut_functor_map_hom.{u, u + 1, u, u + 1} L (FGModuleCat.{u} L)
    (Units.map f.toMonoidHom a) _

/-- The actual scalar K1-to-K2 action commutes with literal tensor extension
and maps its original scalar coefficient by the same field homomorphism. -/
theorem scalarAction_natural (a : Fˣ)
    (z : (abelianExactStructure (FGModuleCat.{u} F)).SmallK.{u + 1} 1) :
    (FGModuleCat.finiteModuleExtensionExact f).smallKMap.{u + 1} 2
        (ScalarUnit.upperFiniteModuleKOneAction F a z) =
      ScalarUnit.upperFiniteModuleKOneAction L (Units.map f.toMonoidHom a)
        ((FGModuleCat.finiteModuleExtensionExact f).smallKMap.{u + 1} 1 z) :=
  IdentityAutomorphism.kOneAction_natural.{u + 1, u + 1}
    (FGModuleCat.finiteModuleExtensionExact f).smallModel.{u + 1}
    (smallModelScalarNatAut.{u, u + 1, u, u + 1} F (FGModuleCat.{u} F) a)
    (smallModelScalarNatAut.{u, u + 1, u, u + 1} L (FGModuleCat.{u} L) (Units.map f.toMonoidHom a))
    (extension_small_scalar f a) z

/-- Literal field extension preserves the actual ordered product of units. -/
theorem unitProduct_natural (a b : Fˣ) :
    (FGModuleCat.finiteModuleExtensionExact f).smallKMap.{u + 1} 2 (unitProduct F a b) =
      unitProduct L (Units.map f.toMonoidHom a) (Units.map f.toMonoidHom b) := by
  unfold unitProduct
  rw [scalarAction_natural, positiveUnitKOne_natural]

end FGModuleCat.FieldSymbols
