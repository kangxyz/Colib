/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Transport of exactness along group equivalences

Commuting group equivalences identify the range-kernel exactness of two
composable homomorphisms. This is an algebraic fact independent of K-theory.

Adapted from `Quillen/Aglib/Algebra/Group/ExactTransport.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The two identical source proofs are
unified under the native group-homomorphism namespace, allowing independent
universes for the six groups.
-/

@[expose] public section

universe u₁ u₂ u₃ v₁ v₂ v₃

namespace MonoidHom

/-- Commuting group equivalences reflect range-kernel exactness. -/
theorem range_eq_ker_of_equiv
    {A : Type u₁} {B : Type u₂} {C : Type u₃}
    {A' : Type v₁} {B' : Type v₂} {C' : Type v₃}
    [Group A] [Group B] [Group C] [Group A'] [Group B'] [Group C']
    (i : A →* B) (f : B →* C) (i' : A' →* B') (f' : B' →* C')
    (eA : A ≃* A') (eB : B ≃* B') (eC : C ≃* C')
    (hi : ∀ a, eB (i a) = i' (eA a))
    (hf : ∀ b, eC (f b) = f' (eB b))
    (h : i'.range = f'.ker) : i.range = f.ker := by
  ext b
  rw [MonoidHom.mem_range, MonoidHom.mem_ker]
  constructor
  · rintro ⟨a, rfl⟩
    apply eC.injective
    rw [map_one, hf, hi]
    have hx : i' (eA a) ∈ i'.range := ⟨eA a, rfl⟩
    rw [h] at hx
    exact hx
  · intro hb
    have hx : eB b ∈ i'.range := by
      rw [h]
      change f' (eB b) = 1
      rw [← hf, hb, map_one]
    obtain ⟨a, ha⟩ := hx
    refine ⟨eA.symm a, eB.injective ?_⟩
    rw [hi, eA.apply_symm_apply, ha]

end MonoidHom
