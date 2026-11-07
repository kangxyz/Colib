/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.Quillen.Field.SteinbergFiberComparison

/-! Regression checks for the actual stable fiber and original right-module Q.K₂.
No perfectness, Matsumoto conclusion or supplied comparison is a hypothesis. -/

noncomputable section
universe u
open CategoryTheory Topology
open ModuleCat.FiniteProjective ModuleCat.FiniteProjective.StableCompletion

example (F : Type u) [Field F] :
    Function.Surjective (stableFiberToElementary F) :=
  stableFiberToElementary_surjective F

example (F : Type u) [Field F] :
    (stableFiberToElementary F).comp (steinbergToStableFiber F) =
      StableSteinberg.toElementary F :=
  steinbergToStableFiber_over F

example (F : Type u) [Field F] :
    Function.Injective (stableFiberConnecting F) :=
  stableFiberConnecting_injective F

example (F : Type u) [Field F] (a : (StableSteinberg.toElementary F).ker) :
    stableFiberConnecting F ((pathTransportMulEquiv (basepointPath F) 1).symm
      (steinbergKernelToCompletionPiTwo F a)) = steinbergToStableFiber F a :=
  connecting_steinbergKernelToCompletionPiTwo F a

example (F : Type u) [Field F] (a : (StableSteinberg.toElementary F).ker) :
    steinbergKernelToRightProjectiveKTwo F a =
      zeroCompletionPositiveKEquiv F 1 (steinbergKernelToCompletionPiTwo F a) :=
  steinbergKernelToRightProjectiveKTwo_apply F a

example (F : Type u) [Field F] :
    (StableSteinberg.toElementary F).ker →* (exactStructure Fᵐᵒᵖ).K 2 :=
  steinbergKernelToRightProjectiveKTwo F
