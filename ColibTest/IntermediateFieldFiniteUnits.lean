/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.FieldTheory.IntermediateField.FiniteUnits

universe u v w

variable {k : Type u} {E : Type v} [Field k] [Field E]
variable [Algebra k E] [Algebra.IsAlgebraic k E]

example {ι : Type w} [Finite ι] (a : ι → Eˣ) :
    ∃ S : IntermediateField k E, FiniteDimensional k S ∧
      ∃ b : ι → Sˣ, ∀ i, Units.map S.val.toRingHom.toMonoidHom (b i) = a i := by
  obtain ⟨S, hS, b, hb⟩ := IntermediateField.exists_finite_units k E a
  exact ⟨S, hS, b, fun i => congrFun hb i⟩

example (a : Fin 0 → Eˣ) :
    ∃ S : IntermediateField k E, FiniteDimensional k S ∧
      ∃ b : Fin 0 → Sˣ, Units.map S.val.toRingHom.toMonoidHom ∘ b = a :=
  IntermediateField.exists_finite_units k E a
