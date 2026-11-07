/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Colib.KTheory.Quillen.Field.SteinbergFiberNaturality

/-! # Regression examples for the actual scalar-change comparison squares -/

open CategoryTheory Topology
open ModuleCat.FiniteProjective ModuleCat.FiniteProjective.StableCompletion

attribute [local instance] CategoryTheory.Limits.hasBinaryBiproducts_of_finite_biproducts
  categoryDirectSumMonoidal directSumMonoidal rightBaseChangeMonoidal

universe u

section Rings

variable {R S : Type u} [Ring R] [Ring S] (f : R →+* S)

example (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (completionBaseChange f).map ((stageAction R n g).asHom) ≫ (stageBaseChangeIso f n).hom =
      (stageBaseChangeIso f n).hom ≫
        (stageAction S n (StableGeneralLinear.finiteMap f n g)).asHom :=
  stageBaseChangeIso_action f n g

example (n : ℕ) :
    (completionBaseChange f).map (stageArrow R n) ≫ (stageBaseChangeIso f (n + 1)).hom =
      (stageBaseChangeIso f n).hom ≫ stageArrow S n :=
  stageBaseChangeIso_successor f n

example : stageBaseChangeIso f 0 = completionBaseChangeZeroIso f :=
  stageBaseChangeIso_zero f

example (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (ZeroComponent R) (zeroBase R)) :
    zeroCompletionPositiveKEquiv S n
      (pathTransportMulEquiv (zeroCompletionBaseChangeBasepointPath f) n
        (HomotopyGroup.mapHom (N := Fin (n + 1)) (zeroCompletionBaseChangeMap f) rfl a)) =
      (rightBaseChangeExact f).KMap (n + 1) (zeroCompletionPositiveKEquiv R n a) :=
  zeroCompletionPositiveKEquiv_baseChange f n a

example :
    ((pathTransportMulEquiv (zeroCompletionBaseChangeBasepointPath f) 0).toMonoidHom.comp
      (HomotopyGroup.piMap 0 (zeroCompletionBaseChangeMap f) (x := zeroBase R) rfl)).comp
        (stablePiOneMap R) =
      (stablePiOneMap S).comp
        (HomotopyGroup.piMap 0 (classifyingSpaceMap (StableGeneralLinear.map f).toFunctor).hom
          (stableRingMap_point f)) :=
  stablePiOneMap_ringMap f

end Rings

section Fields

variable {F L : Type u} [Field F] [Field L] (f : F →+* L)

example :
    (stableFiberToElementary L).comp (stableFiberPiOneMap f) =
      (StableSteinberg.elementaryMap f).comp (stableFiberToElementary F) :=
  stableFiberToElementary_naturality f

example (a : (StableSteinberg.toElementary F).ker) :
    (rightBaseChangeExact f).KMap 2 (steinbergKernelToRightProjectiveKTwo F a) =
      steinbergKernelToRightProjectiveKTwo L (StableSteinberg.toElementaryKernelMap f a) :=
  steinbergKernelToRightProjectiveKTwo_naturality f a

example :
    ((rightBaseChangeExact f).KMap 2).comp (steinbergKernelToRightProjectiveKTwo F) =
      (steinbergKernelToRightProjectiveKTwo L).comp (StableSteinberg.toElementaryKernelMap f) :=
  steinbergKernelToRightProjectiveKTwo_naturality_hom f

end Fields
