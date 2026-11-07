/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Group.Submonoid.Membership
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Uniform annihilators of finite modules

For a finite module, elementwise annihilation by elements of an arbitrary submonoid is
equivalent to annihilation of the whole module by one element of that submonoid. For the
submonoid of powers of an element, this is exactly annihilation by one uniform natural power.
The exponent may be zero, and the submonoid may contain zero.

## Implementation provenance

This supplies the finite-generation support argument used in
`Quillen/GTheory/FiniteModules/LocalizationSequence.lean` and
`Quillen/Aglib/Algebra/Category/FGModuleCat/SmallModelLocalization.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The proof is expressed directly with Mathlib's
`Module.Finite.exists_fin`, finite products, and `Submodule.span_induction`, without any
replacement torsion predicate, module, or categorical model.
-/

@[expose] public section

universe u v

open scoped BigOperators

namespace Module.Finite

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  [Module.Finite R M]

/-- A finite module is elementwise annihilated by a submonoid if and only if a single
element of that submonoid annihilates the whole module. -/
theorem forall_exists_smul_eq_zero_iff (S : Submonoid R) :
    (∀ x : M, ∃ s : S, (s : R) • x = 0) ↔ ∃ s : S, ∀ x : M, (s : R) • x = 0 := by
  classical
  constructor
  · intro h
    obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := R) (M := M)
    choose s hs using fun i : Fin n => h (g i)
    refine ⟨∏ i, s i, ?_⟩
    have hgen (i : Fin n) : (∏ j, (s j : R)) • g i = 0 := by
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_smul, hs i, smul_zero]
    intro x
    rw [Submonoid.coe_finsetProd]
    have hx : x ∈ Submodule.span R (Set.range g) := by
      rw [hg]
      exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hgen i
    | zero => exact smul_zero _
    | add x y hx hy hx' hy' => rw [smul_add, hx', hy', add_zero]
    | smul a x hx hx' => rw [smul_comm, hx', smul_zero]
  · rintro ⟨s, hs⟩ x
    exact ⟨s, hs x⟩

/-- For a finite module, torsion by the submonoid of powers is exactly annihilation of the
whole module by one natural power, including exponent zero. -/
theorem forall_exists_smul_eq_zero_powers_iff (r : R) :
    (∀ x : M, ∃ s : Submonoid.powers r, (s : R) • x = 0) ↔
      ∃ n : ℕ, ∀ x : M, r ^ n • x = 0 := by
  rw [forall_exists_smul_eq_zero_iff]
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (s : R) r).mp s.property
    refine ⟨n, fun x => ?_⟩
    rw [hn]
    exact hs x
  · rintro ⟨n, hn⟩
    exact ⟨⟨r ^ n, (Submonoid.mem_powers_iff _ _).mpr ⟨n, rfl⟩⟩, hn⟩

/-- Elementwise power torsion of a finite module admits one uniform natural exponent. -/
theorem forall_exists_pow_smul_eq_zero_iff (r : R) :
    (∀ x : M, ∃ n : ℕ, r ^ n • x = 0) ↔ ∃ n : ℕ, ∀ x : M, r ^ n • x = 0 := by
  rw [← forall_exists_smul_eq_zero_powers_iff]
  constructor
  · intro h x
    obtain ⟨n, hn⟩ := h x
    exact ⟨⟨r ^ n, (Submonoid.mem_powers_iff _ _).mpr ⟨n, rfl⟩⟩, hn⟩
  · intro h x
    obtain ⟨s, hs⟩ := h x
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (s : R) r).mp s.property
    refine ⟨n, ?_⟩
    rw [hn]
    exact hs

end Module.Finite
