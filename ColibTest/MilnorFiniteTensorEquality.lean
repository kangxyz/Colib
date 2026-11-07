/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.MilnorK.FiniteTensorEquality

universe u v

variable {k : Type u} {E : Type v} [Field k] [Field E]
variable [Algebra k E] [Algebra.IsAlgebraic k E]

example (S : IntermediateField k E) [FiniteDimensional k S]
    (x y : MilnorKTensorAlgebra S)
    (hxy : milnorKTensorMap S.val.toRingHom x = milnorKTensorMap S.val.toRingHom y) :
    ∃ T : IntermediateField k E, FiniteDimensional k T ∧
      ∃ hST : S ≤ T,
        milnorKTensorMap (IntermediateField.inclusion hST).toRingHom x =
          milnorKTensorMap (IntermediateField.inclusion hST).toRingHom y :=
  exists_finite_milnorKTensor_eq k E S x y hxy

example (S : IntermediateField k E) [FiniteDimensional k S]
    (x : MilnorKTensorAlgebra S) (hx : milnorKTensorMap S.val.toRingHom x = 0) :
    ∃ T : IntermediateField k E, FiniteDimensional k T ∧
      ∃ hST : S ≤ T,
        milnorKTensorMap (IntermediateField.inclusion hST).toRingHom x = 0 := by
  obtain ⟨T, hT, hST, hzero⟩ := exists_finite_milnorKTensor_eq k E S x 0
    (by simpa only [map_zero] using hx)
  exact ⟨T, hT, hST, by simpa only [map_zero] using hzero⟩
