/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.GroupTheory.IsPerfect

/-!
# Surjectivity of lifts across a central kernel

If a group homomorphism covers a quotient whose kernel is central, its range
contains the target commutator subgroup. A perfect target therefore makes
that same homomorphism surjective. The three groups have independent universes.

Adapted from `Quillen/Aglib/Algebra/Group/Hom/CentralLifts.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section

universe u v w
open scoped commutatorElement

namespace MonoidHom
variable {S : Type u} {H : Type v} {E : Type w} [Group S] [Group H] [Group E]

/-- Covering a quotient with central kernel puts every target commutator in the original range. -/
theorem commutator_le_range_of_central_ker (f : S →* H) (p : H →* E)
    (hc : p.ker ≤ Subgroup.center H) (hs : Function.Surjective (p.comp f)) :
    commutator H ≤ f.range := by
  rw [commutator_def]
  apply Subgroup.commutator_le.mpr
  intro a _ b _
  obtain ⟨s, hsa⟩ := hs (p a)
  obtain ⟨t, ht⟩ := hs (p b)
  change p (f s) = p a at hsa
  change p (f t) = p b at ht
  let z := a * (f s)⁻¹
  let z' := b * (f t)⁻¹
  have hz : z ∈ Subgroup.center H := hc (by
    change p z = 1
    simp only [z, map_mul, map_inv, hsa, mul_inv_cancel])
  have hz' : z' ∈ Subgroup.center H := hc (by
    change p z' = 1
    simp only [z', map_mul, map_inv, ht, mul_inv_cancel])
  have ha : a = z * f s := by simp [z, mul_assoc]
  have hb : b = z' * f t := by simp [z', mul_assoc]
  have hzComm (c : H) : ⁅z, c⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr ((Subgroup.mem_center_iff.mp hz c).symm)
  have hz'Comm (c : H) : ⁅c, z'⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz' c)
  have he : ⁅a, b⁆ = ⁅f s, f t⁆ := by
    rw [ha, hb, commutatorElement_mul_left_eq_conj_mul, hzComm, mul_one,
      ← Subgroup.mem_center_iff.mp hz ⁅f s, z' * f t⁆]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
    rw [commutatorElement_mul_right_eq_mul_conj, hz'Comm, one_mul,
      ← Subgroup.mem_center_iff.mp hz' ⁅f s, f t⁆]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  exact ⟨⁅s, t⁆, (map_commutatorElement f s t).trans he.symm⟩

/-- A lift covering a central quotient is surjective when its actual target group is perfect. -/
theorem surjective_of_central_ker_of_surjective_comp [Group.IsPerfect H]
    (f : S →* H) (p : H →* E) (hc : p.ker ≤ Subgroup.center H)
    (hs : Function.Surjective (p.comp f)) : Function.Surjective f := by
  intro h
  exact commutator_le_range_of_central_ker f p hc hs (by
    rw [Group.IsPerfect.commutator_eq_top]
    trivial)

end MonoidHom
