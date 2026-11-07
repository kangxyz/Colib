/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.QuillenSurjectivity
import Colib.Topology.Homotopy.HomotopyGroup.Loop.Reversal
import Colib.Topology.Homotopy.HomotopyGroup.Loop.LeftComponentTranslation

/-!
# Actual Milnor-to-Quillen surjectivity

Every field and its original upper SmallModel universe are retained. Importing both
loop branches also checks that reversal has a single native declaration owner.
-/

noncomputable section
universe u
open CategoryTheory CategoryTheory.ExactCategory
open ModuleCat.FiniteProjective.StableCompletion
attribute [local instance] StableSteinberg.kernelCommGroup Abelian.hasFiniteBiproducts

variable (F : Type u) [Field F]

example : Function.Surjective (steinbergToStableFiber F) :=
  steinbergToStableFiber_surjective F

example (a : (ModuleCat.FiniteProjective.exactStructure.{u, u} Fᵐᵒᵖ).K 2) :
    ∃ b : MilnorKTheory F 2, (MilnorKTheory.toRightProjectiveKTwo F b).toMul = a := by
  obtain ⟨b, hb⟩ := MilnorKTheory.toRightProjectiveKTwo_surjective F (Additive.ofMul a)
  exact ⟨b, congrArg Additive.toMul hb⟩

example (a : (abelianExactStructure (FGModuleCat.{u} F)).SmallK.{u + 1} 2) :
    ∃ b : MilnorKTheory F 2, (MilnorKTheory.toUpperModuleKTwo F b).toMul = a := by
  obtain ⟨b, hb⟩ := MilnorKTheory.toUpperModuleKTwo_surjective F (Additive.ofMul a)
  exact ⟨b, congrArg Additive.toMul hb⟩

example (a b : Fˣ) :
    MilnorKTheory.toRightProjectiveKTwo F (milnorKTupleSymbol ![a, b]) = Additive.ofMul
      (steinbergKernelToRightProjectiveKTwo F (StableSteinberg.torusDefectKernel a b)) :=
  MilnorKTheory.toRightProjectiveKTwo_pair F a b
