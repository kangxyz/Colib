/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Finite fields of definition for units

A finite family of units in an algebraic extension is the literal image of a
family of units in one finite intermediate field. The field is the native
`IntermediateField.adjoin` of their values. No separability hypothesis is used.

This generalizes the tuple lemma in `Aglib.KTheory.MilnorK.FiniteRelationDescent`
at revision `101dbb8564fb0e29f28cfcb79168d878b5ab489f`, lines 83-100, to an
arbitrary finite index type, using the same intermediate-field construction.
-/

@[expose] public noncomputable section

universe u v w

namespace IntermediateField

variable (k : Type u) (E : Type v) [Field k] [Field E]
variable [Algebra k E] [Algebra.IsAlgebraic k E]

/-- Finitely many actual units in an algebraic extension have simultaneous
preimages in the units of one finite intermediate field. -/
theorem exists_finite_units {ι : Type w} [Finite ι] (a : ι → Eˣ) :
    ∃ S : IntermediateField k E, FiniteDimensional k S ∧
      ∃ b : ι → Sˣ, Units.map S.val.toRingHom.toMonoidHom ∘ b = a := by
  let S := IntermediateField.adjoin k (Set.range fun i => (a i : E))
  have hS : FiniteDimensional k S := IntermediateField.finiteDimensional_adjoin
    (fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
  have ha (i : ι) : (a i : E) ∈ S :=
    IntermediateField.subset_adjoin k _ ⟨i, rfl⟩
  let b : ι → Sˣ := fun i => Units.mk0 ⟨(a i : E), ha i⟩ (by
    intro hz
    exact (a i).ne_zero (congrArg (fun x : S => (x : E)) hz))
  refine ⟨S, hS, b, ?_⟩
  funext i
  apply Units.ext
  rfl

end IntermediateField
