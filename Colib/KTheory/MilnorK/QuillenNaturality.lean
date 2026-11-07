/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.MilnorK.QuillenComparison
public import Colib.KTheory.Quillen.Field.SteinbergFiberNaturality

/-!
# Scalar extension for the original Milnor-to-Quillen maps

The actual right-projective K-map and literal upper SmallModel tensor extension
commute with the native Milnor map. The kernel map retains its existing owner.

Source: `Quillen/KTheory/Field/MilnorKTwoComparison.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, naturality clauses.
-/

@[expose] public noncomputable section
universe u
open CategoryTheory ModuleCat.FiniteProjective.StableCompletion
attribute [local instance] StableSteinberg.kernelCommGroup Abelian.hasFiniteBiproducts

namespace MilnorKTheory
variable {F L : Type u} [Field F] [Field L] (f : F →+* L)

/-- The original right-projective scalar extension commutes with the canonical Milnor map. -/
theorem toRightProjectiveKTwo_naturality (a : MilnorKTheory F 2) :
    ((ModuleCat.FiniteProjective.rightBaseChangeExact f).KMap 2).toAdditive
        (toRightProjectiveKTwo F a) =
      toRightProjectiveKTwo L ((milnorKTheoryMap f 2).toAddMonoidHom a) := by
  have hk : (StableSteinberg.toElementaryKernelMap f).toAdditive
      (StableSteinberg.milnorToKernel F a) =
        StableSteinberg.milnorToKernel L ((milnorKTheoryMap f 2).toAddMonoidHom a) :=
    DFunLike.congr_fun (StableSteinberg.milnorToKernel_naturality f) a
  change ((ModuleCat.FiniteProjective.rightBaseChangeExact f).KMap 2).toAdditive
      ((steinbergKernelToRightProjectiveKTwo F).toAdditive
        (StableSteinberg.milnorToKernel F a)) =
    (steinbergKernelToRightProjectiveKTwo L).toAdditive
      (StableSteinberg.milnorToKernel L ((milnorKTheoryMap f 2).toAddMonoidHom a))
  calc
    _ = (steinbergKernelToRightProjectiveKTwo L).toAdditive
        ((StableSteinberg.toElementaryKernelMap f).toAdditive
          (StableSteinberg.milnorToKernel F a)) :=
      congrArg Additive.ofMul (steinbergKernelToRightProjectiveKTwo_naturality f
        (StableSteinberg.milnorToKernel F a).toMul)
    _ = _ := congrArg (steinbergKernelToRightProjectiveKTwo L).toAdditive hk

/-- Homomorphism form of the original right-projective field-extension square. -/
theorem toRightProjectiveKTwo_naturality_hom :
    (((ModuleCat.FiniteProjective.rightBaseChangeExact f).KMap 2).toAdditive).comp
        (toRightProjectiveKTwo F) =
      (toRightProjectiveKTwo L).comp ((milnorKTheoryMap f 2).toAddMonoidHom) := by
  apply AddMonoidHom.ext
  intro a
  exact toRightProjectiveKTwo_naturality f a

/-- Literal tensor extension and the original upper-model transport give the actual
finite-module square. -/
theorem toUpperModuleKTwo_naturality (a : MilnorKTheory F 2) :
    ((FGModuleCat.finiteModuleExtensionExact f).smallKMap.{u + 1} 2).toAdditive
        (toUpperModuleKTwo F a) =
      toUpperModuleKTwo L ((milnorKTheoryMap f 2).toAddMonoidHom a) := by
  have h := congrArg Additive.toMul (toRightProjectiveKTwo_naturality f a)
  change (ModuleCat.FiniteProjective.rightBaseChangeExact f).KMap 2
      (toRightProjectiveKTwo F a).toMul =
    (toRightProjectiveKTwo L ((milnorKTheoryMap f 2).toAddMonoidHom a)).toMul at h
  exact congrArg Additive.ofMul
    ((FGModuleCat.rightProjectiveUpperModuleKEquiv_baseChange f 2
      (toRightProjectiveKTwo F a).toMul).symm.trans
      (congrArg (FGModuleCat.rightProjectiveUpperModuleKEquiv L 2) h))

/-- Homomorphism form of the original upper finite-module field-extension square. -/
theorem toUpperModuleKTwo_naturality_hom :
    (((FGModuleCat.finiteModuleExtensionExact f).smallKMap.{u + 1} 2).toAdditive).comp
        (toUpperModuleKTwo F) =
      (toUpperModuleKTwo L).comp ((milnorKTheoryMap f 2).toAddMonoidHom) := by
  apply AddMonoidHom.ext
  intro a
  exact toUpperModuleKTwo_naturality f a

end MilnorKTheory
