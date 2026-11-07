/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.GroupTheory.Steinberg.Matsumoto.NormalizerMatrix
import Colib.KTheory.MilnorK.Steinberg

/-! Regression checks on the native Milnor coefficient and its positive marking.
These do not assert injectivity of the stable Steinberg kernel map. -/

noncomputable section

universe u

open StableSteinberg.RootCoordinate

variable {F : Type u} [Field F]

example (n : ℕ) : Function.Injective (normalizerCoefficient F n) :=
  normalizerCoefficient_injective F n

example (n : ℕ) :
    (normalizerToGL F n).ker = (normalizerCoefficient F n).range :=
  normalizerToGL_ker F n

example (a b : Fˣ) :
    torusLift F 2 (coroot01 F a) * torusLift F 2 (coroot01 F b) *
      (torusLift F 2 (coroot01 F (a * b)))⁻¹ =
        coefficient F 2 (Multiplicative.ofAdd (milnorKTupleSymbol ![a, b])) :=
  marked_defect F a b

example (a b : Fˣ) :
    StableSteinberg.milnorToKernel F (pair F a b) =
      Additive.ofMul (StableSteinberg.torusDefectKernel a b) :=
  StableSteinberg.milnorToKernel_pair a b

example {n : ℕ} (i : Fin n) :
    normalizerW F i (-1) ^ 4 = 1 ↔
      (milnorKTupleSymbol ![-1, -1] : MilnorKTheory F 2) = 0 :=
  normalizerW_neg_one_pow_four_eq_one_iff F i
