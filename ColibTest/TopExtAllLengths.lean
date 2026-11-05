/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Colib.RingTheory.Koszul.TopExtAllLengths

/-! Empty-sequence and positive-branch regression tests for the quotient endpoints. -/

open CategoryTheory CategoryTheory.Abelian
open scoped Pointwise

universe u w

variable {R : Type u} [CommRing R] [HasExt.{w} (ModuleCat.{u} R)]

example (f : Fin 0 → R) (hf : Koszul.IsKoszulRegular f) (N : ModuleCat.{u} R) (x : N) :
    Koszul.seqTopExtClass f hf N x = 0 ↔ x = 0 :=
  Koszul.seqTopExtClass_empty_eq_zero_iff f hf N x

example {n : ℕ} (f : Fin n → R) (hf : Koszul.IsKoszulRegular f)
    (N : ModuleCat.{u} R) (x : N) :
    Koszul.seqTopExtQuotientLinearEquivAll f hf N (Submodule.Quotient.mk x) =
      Koszul.seqTopExtClass f hf N x :=
  Koszul.seqTopExtQuotientLinearEquivAll_apply_mk f hf N x

example (f : Fin 0 → R) (hf : Koszul.IsKoszulRegular f) (N : ModuleCat.{u} R) :
    Nonempty ((N ⧸ (⊥ : Submodule R N)) ≃ₗ[R]
      Ext (ModuleCat.of R (R ⧸ (⊥ : Ideal R))) N 0) := by
  have e := Koszul.seqTopExtLinearEquivAll f hf N
  have hI : Ideal.span (Set.range f) = (⊥ : Ideal R) := by
    rw [Set.range_eq_empty, Ideal.span_empty]
  rw [hI, Submodule.bot_smul] at e
  exact ⟨e⟩

example {n : ℕ} (f : Fin (n + 1) → R) (hf : Koszul.IsKoszulRegular f)
    (N : ModuleCat.{u} R) :
    Koszul.seqTopExtQuotientLinearEquivAll f hf N =
      Koszul.seqTopExtQuotientLinearEquiv f hf N := rfl

example (f : Fin 0 → R) (hf : Koszul.IsKoszulRegular f) (N : ModuleCat.{u} R)
    (r : R ⧸ Ideal.span (Set.range f))
    (x : N ⧸ (Ideal.span (Set.range f) • (⊤ : Submodule R N))) :
    letI := Ext.quotientSourceModule (Ideal.span (Set.range f)) N 0
    Koszul.seqTopExtQuotientLinearEquivAll f hf N (r • x) =
      r • Koszul.seqTopExtQuotientLinearEquivAll f hf N x := by
  let := Ext.quotientSourceModule (Ideal.span (Set.range f)) N 0
  exact (Koszul.seqTopExtQuotientLinearEquivAll f hf N).map_smul r x
