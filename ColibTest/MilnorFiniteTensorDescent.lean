/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.FiniteTensorDescent

universe u v

variable {k : Type u} {E : Type v} [Field k] [Field E]
variable [Algebra k E] [Algebra.IsAlgebraic k E]

example (x : MilnorKTensorAlgebra E) :
    ∃ S : IntermediateField k E, FiniteDimensional k S ∧
      ∃ y : MilnorKTensorAlgebra S, milnorKTensorMap S.val.toRingHom y = x :=
  exists_finite_milnorKTensor k E x

example (x : MilnorKTensorAlgebra E) (hx : x ∈ milnorKSteinbergIdeal E) :
    ∃ S : IntermediateField k E, FiniteDimensional k S ∧
      ∃ y : MilnorKTensorAlgebra S, y ∈ milnorKSteinbergIdeal S ∧
        milnorKTensorMap S.val.toRingHom y = x :=
  exists_finite_milnorKSteinbergIdeal k E x hx

example (a x b : MilnorKTensorAlgebra E) (hx : x ∈ milnorKSteinbergRelations E) :
    ∃ S : IntermediateField k E, FiniteDimensional k S ∧
      ∃ y : MilnorKTensorAlgebra S, y ∈ milnorKSteinbergIdeal S ∧
        milnorKTensorMap S.val.toRingHom y = a * x * b := by
  apply exists_finite_milnorKSteinbergIdeal k E
  exact (milnorKSteinbergIdeal E).mul_mem_right _ _
    ((milnorKSteinbergIdeal E).mul_mem_left _ _ (TwoSidedIdeal.subset_span hx))

example {S T : IntermediateField k E} (h : S ≤ T) (x : MilnorKTensorAlgebra S) :
    milnorKTensorMap T.val.toRingHom
        (milnorKTensorMap (IntermediateField.inclusion h).toRingHom x) =
      milnorKTensorMap S.val.toRingHom x :=
  milnorKTensorMap_val_inclusion h x
