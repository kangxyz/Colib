/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.FiniteRelationDescent

universe u v

variable {k : Type u} {E : Type v} [Field k] [Field E]
variable [Algebra k E] [Algebra.IsAlgebraic k E]

example (n : ℕ) (x : MilnorKTheory k n)
    (hx : milnorKTheoryMap (algebraMap k E) n x = 0) :
    ∃ S : IntermediateField k E, FiniteDimensional k S ∧
      milnorKTheoryMap (algebraMap k S) n x = 0 :=
  exists_finite_intermediate_milnorKTheoryMap_eq_zero k E n x hx

example (x y : MilnorKTheory k 0)
    (hxy : milnorKTheoryMap (algebraMap k E) 0 x =
      milnorKTheoryMap (algebraMap k E) 0 y) :
    ∃ S : IntermediateField k E, FiniteDimensional k S ∧
      milnorKTheoryMap (algebraMap k S) 0 x = milnorKTheoryMap (algebraMap k S) 0 y :=
  exists_finite_intermediate_milnorKTheoryMap_eq k E 0 x y hxy

example (S : IntermediateField k E) [FiniteDimensional k S]
    (n : ℕ) (x y : MilnorKTheory S n)
    (hxy : milnorKTheoryMap S.val.toRingHom n x =
      milnorKTheoryMap S.val.toRingHom n y) :
    ∃ T : IntermediateField k E, FiniteDimensional k T ∧
      ∃ hST : S ≤ T,
        milnorKTheoryMap (IntermediateField.inclusion hST).toRingHom n x =
          milnorKTheoryMap (IntermediateField.inclusion hST).toRingHom n y :=
  exists_finite_milnorKTheory_eq_over k E S n x y hxy

example (S : IntermediateField k E) [FiniteDimensional k S]
    (x : MilnorKTensorAlgebra S)
    (hx : milnorKTensorMap S.val.toRingHom x ∈ milnorKSteinbergIdeal E) :
    ∃ T : IntermediateField k E, FiniteDimensional k T ∧
      ∃ hST : S ≤ T,
        milnorKTensorMap (IntermediateField.inclusion hST).toRingHom x ∈
          milnorKSteinbergIdeal T :=
  exists_finite_milnorKTensor_mem_steinberg k E S x hx
