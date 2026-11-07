/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.QuillenComparison

/-! Regression checks for the original Milnor maps into actual right-module and
upper finite-module Quillen K₂, including the ordered symbol and inclusion maps. -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.ExactCategory
open ModuleCat.FiniteProjective.StableCompletion
attribute [local instance] Abelian.hasFiniteBiproducts

example (F : Type u) [Field F] : MilnorKTheory F 2 →+
    Additive ((ModuleCat.FiniteProjective.exactStructure.{u, u} Fᵐᵒᵖ).K 2) :=
  MilnorKTheory.toRightProjectiveKTwo F

example (F : Type u) [Field F] (a b : Fˣ) :
    MilnorKTheory.toRightProjectiveKTwo F (milnorKTupleSymbol ![a, b]) = Additive.ofMul
      (steinbergKernelToRightProjectiveKTwo F (StableSteinberg.torusDefectKernel a b)) :=
  MilnorKTheory.toRightProjectiveKTwo_pair F a b

example (F : Type u) [Field F] : MilnorKTheory F 2 →+
    Additive ((abelianExactStructure (FGModuleCat.{u} F)).SmallK.{u+1} 2) :=
  MilnorKTheory.toUpperModuleKTwo F

example (F : Type u) [Field F] (a b : Fˣ) :
    MilnorKTheory.toUpperModuleKTwo F (milnorKTupleSymbol ![a, b]) = Additive.ofMul
      (FGModuleCat.rightProjectiveUpperModuleKEquiv F 2
        (steinbergKernelToRightProjectiveKTwo F (StableSteinberg.torusDefectKernel a b))) :=
  MilnorKTheory.toUpperModuleKTwo_pair F a b

example (F : Type u) [Field F] (a : MilnorKTheory F 2) :
    (abelianExactStructure (FGModuleCat.{u} F)).smallModelToOriginal.{u+1}.commonAmbientKMap
      2 (MilnorKTheory.toUpperModuleKTwo F a).toMul =
      (FGModuleCat.finiteModuleRingExact (RingEquiv.toOpposite F)).KMap 2
        ((ModuleCat.FiniteProjective.toFiniteModuleExact Fᵐᵒᵖ).KMap 2
          (MilnorKTheory.toRightProjectiveKTwo F a).toMul) :=
  MilnorKTheory.toUpperModuleKTwo_toOriginal F a
