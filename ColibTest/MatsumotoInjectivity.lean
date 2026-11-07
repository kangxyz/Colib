/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.MilnorK.Steinberg.Equivalence

/-! Checks on the concrete characteristic-zero detector and canonical kernel equivalence. -/

noncomputable section

universe u v

open StableSteinberg

variable {F : Type u} [Field F] [CharZero F]

example : Function.Injective (milnorToKernel F) := milnorToKernel_injective_charZero F

example : Function.Bijective (milnorToKernel F) := milnorToKernel_bijective_charZero F

example : (milnorKernelEquiv F).toAddMonoidHom = milnorToKernel F := rfl

example (a b : Fˣ) :
    milnorKernelEquiv F (milnorKTupleSymbol ![a, b]) =
      Additive.ofMul (torusDefectKernel a b) := milnorKernelEquiv_pair F a b

example (a b : Fˣ) :
    (milnorKernelEquiv F).symm (Additive.ofMul (torusDefectKernel a b)) =
      milnorKTupleSymbol ![a, b] := milnorKernelEquiv_symm_torusDefectKernel F a b

example {L : Type v} [Field L] [CharZero L] (f : F →+* L) :
    ((toElementaryKernelMap f).toAdditive).comp (milnorKernelEquiv F).toAddMonoidHom =
      (milnorKernelEquiv L).toAddMonoidHom.comp (milnorKTheoryMap f 2).toAddMonoidHom :=
  milnorKernelEquiv_naturality f

example (n : ℕ) (hn : 3 ≤ n) (a b : Fˣ) :
    CommutatorDetectorTransfer.finiteCommutator (RootCoordinate.finiteRootOperator F) n hn a b =
      RootCoordinate.finiteCoefficientOperator F n
        (Multiplicative.ofAdd (milnorKTupleSymbol ![a, b])) :=
  RootCoordinate.finiteRootOperator_commutator_mark F n hn a b
