/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.FiniteClassDescent

universe u v w

variable {k : Type u} {E : Type v} [Field k] [Field E]
variable [Algebra k E] [Algebra.IsAlgebraic k E]

example (x : MilnorKTheory E 0) :
    ∃ S : IntermediateField k E, FiniteDimensional k S ∧
      ∃ y : MilnorKTheory S 0, milnorKTheoryMap S.val.toRingHom 0 y = x :=
  exists_finite_milnorKTheory k E 0 x

example {ι : Type w} [Finite ι] (d : ι → ℕ) (x : ∀ i, MilnorKTheory E (d i)) :
    ∃ S : IntermediateField k E, FiniteDimensional k S ∧
      ∃ y : ∀ i, MilnorKTheory S (d i),
        ∀ i, milnorKTheoryMap S.val.toRingHom (d i) (y i) = x i :=
  exists_finite_milnorKTheory_family k E d x

example {ι : Type w} [Finite ι] (S₀ : IntermediateField k E)
    [FiniteDimensional k S₀] (d : ι → ℕ) (x : ∀ i, MilnorKTheory E (d i)) :
    ∃ S : IntermediateField k E, FiniteDimensional k S ∧ S₀ ≤ S ∧
      ∃ y : ∀ i, MilnorKTheory S (d i),
        ∀ i, milnorKTheoryMap S.val.toRingHom (d i) (y i) = x i :=
  exists_finite_milnorKTheory_family_over k E S₀ d x

example {S T : IntermediateField k E} (h : S ≤ T) (n : ℕ) (x : MilnorKTheory S n) :
    milnorKTheoryMap T.val.toRingHom n
        (milnorKTheoryMap (IntermediateField.inclusion h).toRingHom n x) =
      milnorKTheoryMap S.val.toRingHom n x :=
  milnorKTheoryMap_val_inclusion h n x
