/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Resolution.Transport
public import Colib.CategoryTheory.ExactCategory.Resolution.Presentation

/-! Adapted from `Quillen/Aglib/CategoryTheory/ExactCategory/Resolution/Strata.lean`
at pinned Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd.
This module supplies finite-resolution prerequisites, not the Resolution theorem. -/

@[expose] public section
noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) (P : ObjectProperty C)
  [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
section LengthStrata

/-- Each length stratum is replete, by transport of the actual resolution. -/
instance resolutionLength_closedUnderIsomorphisms (n : ℕ) :
    (E.ResolutionLength P n).IsClosedUnderIsomorphisms where
  of_iso e hX := by
    obtain ⟨R, hR⟩ := hX
    exact ⟨R.ofIso e, by simpa using hR⟩

/-- All strata contain zero via the length-zero identity resolution. -/
instance resolutionLength_containsZero (n : ℕ) : (E.ResolutionLength P n).ContainsZero :=
  ⟨⟨0, isZero_zero C, .of_mem P.prop_zero, Nat.zero_le n⟩⟩

omit [P.IsClosedUnderIsomorphisms] [P.ContainsZero] in
lemma le_resolutionLength (n : ℕ) : P ≤ E.ResolutionLength P n :=
  fun _X hX => ⟨.of_mem hX, Nat.zero_le n⟩

lemma resolutionLength_succ_eq (n : ℕ) :
    E.ResolutionLength P (n + 1) = E.ResolutionStep P (E.ResolutionLength P n) := by
  funext X
  exact propext (E.resolutionLength_succ_iff P n X)

end LengthStrata
end CategoryTheory.ExactCategory.ExactStructure
