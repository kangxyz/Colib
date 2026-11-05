/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.MilnorK.Symbols.Ext
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Surjectivity from native tuple symbols

The existing homogeneous symbol extensionality implies that an additive map is surjective
once every tuple symbol lies in its range. The proof uses only Mathlib's quotient by the range;
no new Milnor presentation or generation theorem is introduced.
-/

@[expose] public section

universe u v

variable {k : Type u} [Field k] {A : Type v} [AddCommGroup A] {n : ℕ}

/-- An additive map onto all native tuple symbols is onto the whole homogeneous group. -/
theorem milnorKTheory_surjective_of_tupleSymbol (f : A →+ MilnorKTheory k n)
    (hf : ∀ a : Fin n → kˣ, milnorKTupleSymbol a ∈ f.range) : Function.Surjective f := by
  have h : QuotientAddGroup.mk' f.range = 0 := by
    apply milnorKTheory_addHom_ext
    intro a
    exact (QuotientAddGroup.eq_zero_iff _).mpr (hf a)
  intro x
  exact (QuotientAddGroup.eq_zero_iff x).mp (DFunLike.congr_fun h x)
