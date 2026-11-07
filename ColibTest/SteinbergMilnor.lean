/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Steinberg

noncomputable section

universe u v

open scoped commutatorElement

-- Noncommutative coefficients and their order are retained.
example {R : Type u} [Ring R] (a b : R) :
    ⁅Matrix.GeneralLinearGroup.elementary (0 : Fin 3) 1 (by decide) a,
      Matrix.GeneralLinearGroup.elementary (1 : Fin 3) 2 (by decide) b⁆ =
      Matrix.GeneralLinearGroup.elementary (0 : Fin 3) 2 (by decide) (a * b) :=
  Matrix.GeneralLinearGroup.elementary_commutator _ _ _ _ _ _ _ _

-- Stabilization includes rank zero and preserves each existing finite stage.
example {R : Type u} [Ring R] :
    Function.Injective (StableGeneralLinear.of R 0) :=
  StableGeneralLinear.of_injective R 0

example {R : Type u} [Ring R] :
    Group.IsPerfect (StableGeneralLinear.elementary R) := inferInstance

variable {F : Type u} [Field F]

example : Group.IsPerfect (StableSteinberg.Group F) := inferInstance

example : Function.Surjective (StableSteinberg.toElementary F) :=
  StableSteinberg.toElementary_surjective F

example : (StableSteinberg.toElementary F).ker ≤
    Subgroup.center (StableSteinberg.Group F) :=
  StableSteinberg.ker_toElementary_le_center F

attribute [local instance] StableSteinberg.kernelCommGroup

example (a b : Fˣ) :
    StableSteinberg.milnorToKernel F (milnorKTupleSymbol ![a, b]) =
      Additive.ofMul (StableSteinberg.torusDefectKernel a b) :=
  StableSteinberg.milnorToKernel_pair a b

example (a b : Fˣ) :
    ⁅StableSteinberg.h a, StableSteinberg.h02 b⁆ = StableSteinberg.torusDefect a b :=
  StableSteinberg.commutator_h_h02 a b

example (a b : Fˣ) (hab : (a : F) + (b : F) = 1) :
    StableSteinberg.torusDefect a b = 1 :=
  StableSteinberg.torusDefect_steinberg a b hab

-- No characteristic-zero, infinitude or common-universe condition is used here.
example {L : Type v} [Field L] (f : F →+* L) :
    ((StableSteinberg.toElementaryKernelMap f).toAdditive).comp
        (StableSteinberg.milnorToKernel F) =
      (StableSteinberg.milnorToKernel L).comp (milnorKTheoryMap f 2).toAddMonoidHom :=
  StableSteinberg.milnorToKernel_naturality f

example {L : Type u} [Field L] (f : F →+* L) :
    ((StableSteinberg.toElementaryKernelMap f).toAdditive).comp
        (StableSteinberg.milnorToKernel F) =
      (StableSteinberg.milnorToKernel L).comp (milnorKTransport f 2) :=
  StableSteinberg.milnorToKernel_naturality_transport f
