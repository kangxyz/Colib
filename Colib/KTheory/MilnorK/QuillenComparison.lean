/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.MilnorK.Steinberg
public import Colib.KTheory.Quillen.Field.SteinbergFiberComparison
public import Colib.KTheory.Quillen.Field.UpperModuleComparison

/-! # The original Milnor K₂ maps into actual Quillen K₂

The existing ordered torus-defect map is followed by the genuine stable-fiber
comparison into the original Q-construction of finite projective right modules.
The finite-module map uses the already-proved upper SmallModel comparison, with
its original inclusion and opposite-ring restriction maps.

These are the original forward maps of the intended comparison. No bijectivity,
field-change naturality, or positive scalar-product marking is asserted here.

Source: the construction and ordered-symbol clauses of
`Quillen/KTheory/Field/MilnorKTwoComparison.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Native Milnor symbols and native
`FGModuleCat` replace neither group by a second presentation.
-/
@[expose] public noncomputable section

universe u
open CategoryTheory CategoryTheory.ExactCategory
open ModuleCat.FiniteProjective.StableCompletion
attribute [local instance] StableSteinberg.kernelCommGroup Abelian.hasFiniteBiproducts

namespace MilnorKTheory
variable (F : Type u) [Field F]

/-- The existing native Milnor map followed by the original right-projective K₂ map. -/
def toRightProjectiveKTwo : MilnorKTheory F 2 →+
    Additive ((ModuleCat.FiniteProjective.exactStructure.{u, u} Fᵐᵒᵖ).K 2) :=
  (steinbergKernelToRightProjectiveKTwo F).toAdditive.comp (StableSteinberg.milnorToKernel F)

/-- The original finite-module comparison in the specified upper SmallModel universe. -/
def toUpperModuleKTwo : MilnorKTheory F 2 →+
    Additive ((abelianExactStructure (FGModuleCat.{u} F)).SmallK.{u+1} 2) :=
  (FGModuleCat.rightProjectiveUpperModuleKEquiv F 2).toMonoidHom.toAdditive.comp
    (toRightProjectiveKTwo F)

/-- The right-projective map retains the literal original composite. -/
theorem toRightProjectiveKTwo_apply (a : MilnorKTheory F 2) :
    toRightProjectiveKTwo F a = Additive.ofMul
      (steinbergKernelToRightProjectiveKTwo F (StableSteinberg.milnorToKernel F a).toMul) := rfl

/-- The finite-module map retains the original upper-model equivalence. -/
theorem toUpperModuleKTwo_apply (a : MilnorKTheory F 2) :
    toUpperModuleKTwo F a = Additive.ofMul
      (FGModuleCat.rightProjectiveUpperModuleKEquiv F 2 (toRightProjectiveKTwo F a).toMul) := rfl

/-- Ordered native Milnor symbols retain the actual ordered kernel defect. -/
theorem toRightProjectiveKTwo_symbol (a : Fin 2 → Fˣ) :
    toRightProjectiveKTwo F (milnorKTupleSymbol a) = Additive.ofMul
      (steinbergKernelToRightProjectiveKTwo F
        (StableSteinberg.torusDefectKernel (a 0) (a 1))) := by
  rw [toRightProjectiveKTwo_apply, StableSteinberg.milnorToKernel_symbol]
  rfl

/-- The original ordered pair has its literal torus-defect value in actual Q.K₂. -/
theorem toRightProjectiveKTwo_pair (a b : Fˣ) :
    toRightProjectiveKTwo F (milnorKTupleSymbol ![a, b]) = Additive.ofMul
      (steinbergKernelToRightProjectiveKTwo F (StableSteinberg.torusDefectKernel a b)) :=
  toRightProjectiveKTwo_symbol F ![a, b]

/-- Upper finite-module symbols use the same actual ordered defect and equivalence. -/
theorem toUpperModuleKTwo_symbol (a : Fin 2 → Fˣ) :
    toUpperModuleKTwo F (milnorKTupleSymbol a) = Additive.ofMul
      (FGModuleCat.rightProjectiveUpperModuleKEquiv F 2
        (steinbergKernelToRightProjectiveKTwo F
          (StableSteinberg.torusDefectKernel (a 0) (a 1)))) := by
  rw [toUpperModuleKTwo_apply, toRightProjectiveKTwo_symbol]
  rfl

/-- The ordered upper-model pair retains its original defect and explicit comparison. -/
theorem toUpperModuleKTwo_pair (a b : Fˣ) :
    toUpperModuleKTwo F (milnorKTupleSymbol ![a, b]) = Additive.ofMul
      (FGModuleCat.rightProjectiveUpperModuleKEquiv F 2
        (steinbergKernelToRightProjectiveKTwo F (StableSteinberg.torusDefectKernel a b))) :=
  toUpperModuleKTwo_symbol F ![a, b]

/-- Undoing the upper model exposes the original inclusion and opposite-ring restriction. -/
theorem toUpperModuleKTwo_toOriginal (a : MilnorKTheory F 2) :
    (abelianExactStructure (FGModuleCat.{u} F)).smallModelToOriginal.{u+1}.commonAmbientKMap
      2 (toUpperModuleKTwo F a).toMul =
      (FGModuleCat.finiteModuleRingExact (RingEquiv.toOpposite F)).KMap 2
        ((ModuleCat.FiniteProjective.toFiniteModuleExact Fᵐᵒᵖ).KMap 2
          (toRightProjectiveKTwo F a).toMul) :=
  FGModuleCat.rightProjectiveUpperModuleKEquiv_toOriginal F 2 _

end MilnorKTheory
