/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Symbols.Ext
public import Mathlib.RingTheory.IntegralDomain

/-!
# Milnor K₂ of finite fields

The native Stacks degree-two Milnor group is zero over every finite field,
including the fields with two and three elements. Cyclicity of the unit group
reduces the proof to a diagonal symbol. Skew symmetry and the Steinberg relation
then give a finite-fibre contradiction, with no restriction on characteristic.

This is Steinberg's finite-field calculation as recorded in Milnor (1970),
Section 1, Example 1.5, p. 321. Only its degree-two clause is asserted here.
The cyclic-unit and Steinberg-symbol argument is also given in Weibel,
III, Corollary 6.1.1. It is independent of higher Quillen K-group computations.

Implementation provenance: this adapts
`Quillen/Aglib/KTheory/MilnorK/K2/FiniteField.lean` at revision
`c561118b7795eb9780be9ed391c3251d6a4d0afd` directly to Stacks' actual quotient.
No auxiliary Milnor model or Aglib dependency is introduced.
-/

@[expose] public noncomputable section

universe u

variable {k : Type u} [Field k] [Finite k]

omit [Finite k] in
private theorem milnorKSymbol_pow (a : kˣ) (n : ℕ) :
    milnorKSymbol k (a ^ n) = n • milnorKSymbol k a := by
  simpa only [zpow_natCast, natCast_zsmul] using milnorKSymbol_zpow a (n : ℤ)

private theorem milnorKSymbol_generator_mul_self_eq_zero (t : kˣ)
    (ht : ∀ a : kˣ, ∃ n : ℕ, t ^ n = a) :
    milnorKSymbol k t * milnorKSymbol k t = 0 := by
  classical
  by_contra hs
  let s := milnorKSymbol k t * milnorKSymbol k t
  have htwo : s + s = 0 := milnorKSymbol_mul_add_mul_comm t t
  have hm (n : ℕ) : n • s = 0 ∨ n • s = s := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [succ_nsmul]
      rcases ih with h | h
      · right; simp [h]
      · left; rw [h, htwo]
  have hvalues (a : kˣ) :
      milnorKSymbol k t * milnorKSymbol k a = 0 ∨
        milnorKSymbol k t * milnorKSymbol k a = s := by
    obtain ⟨n, rfl⟩ := ht a
    rw [milnorKSymbol_pow, mul_smul_comm]
    exact hm n
  let N := {a : kˣ // milnorKSymbol k t * milnorKSymbol k a ≠ 0}
  have hne (a : N) : (a.val : k) ≠ 1 := by
    intro h
    apply a.property
    have ha : a.val = 1 := Units.ext h
    rw [ha, milnorKSymbol_one, mul_zero]
  let c (a : N) : kˣ := Units.mk0 (1 - (a.val : k)) (sub_ne_zero.mpr (hne a).symm)
  have hsteinberg (a : N) : milnorKSymbol k a.val * milnorKSymbol k (c a) = 0 :=
    milnorKSymbol_mul_steinberg (add_sub_cancel _ _)
  have hcomplement (a : N) : milnorKSymbol k t * milnorKSymbol k (c a) = 0 := by
    rcases hvalues (c a) with h | h
    · exact h
    · obtain ⟨n, hn⟩ := ht a.val
      have he : milnorKSymbol k a.val * milnorKSymbol k (c a) =
          milnorKSymbol k t * milnorKSymbol k a.val := by
        nth_rw 1 [← hn]
        rw [milnorKSymbol_pow, smul_mul_assoc, h]
        rw [← hn, milnorKSymbol_pow, mul_smul_comm]
      exact (a.property (he.symm.trans (hsteinberg a))).elim
  let f : N → N := fun a => ⟨t * c a, by
    rw [milnorKSymbol_mul, mul_add, hcomplement, add_zero]
    exact hs⟩
  have hfinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Units.ext
    have he : t * c a = t * c b := congrArg Subtype.val hab
    have he' := congrArg Units.val (mul_left_cancel he)
    simp only [c, Units.val_mk0] at he'
    simpa using congrArg (fun x : k => 1 - x) he'
  obtain ⟨a, ha⟩ := (Finite.surjective_of_injective hfinj) (⟨t, hs⟩ : N)
  have he : t * c a = t := congrArg Subtype.val ha
  have he' : c a = 1 := by
    apply mul_left_cancel (a := t)
    simpa using he
  have hz : (a.val : k) = 0 := by
    have hh := congrArg Units.val he'
    simpa only [c, Units.val_mk0, Units.val_one, sub_eq_self] using hh
  exact a.val.ne_zero hz

/-- Every product of two native Milnor symbols over a finite field vanishes. -/
theorem milnorKSymbol_mul_eq_zero_of_finite (a b : kˣ) :
    milnorKSymbol k a * milnorKSymbol k b = 0 := by
  obtain ⟨t, ht⟩ := IsCyclic.exists_generator (α := kˣ)
  have hp (c : kˣ) : ∃ n : ℕ, t ^ n = c :=
    (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr (ht c))
  have hs := milnorKSymbol_generator_mul_self_eq_zero t hp
  obtain ⟨m, rfl⟩ := hp a
  obtain ⟨n, rfl⟩ := hp b
  rw [milnorKSymbol_pow, milnorKSymbol_pow, smul_mul_assoc, mul_smul_comm, hs,
    smul_zero, smul_zero]

/-- Every degree-two tuple symbol in the native homogeneous group vanishes. -/
theorem milnorKTupleSymbol_two_eq_zero_of_finite (a : Fin 2 → kˣ) :
    milnorKTupleSymbol a = 0 := by
  apply Subtype.ext
  change milnorKSymbolProd k (List.ofFn a) = 0
  simpa only [List.ofFn_succ, List.ofFn_zero, milnorKSymbolProd_cons,
    milnorKSymbolProd_nil, mul_one, Fin.succ_zero_eq_one] using
    milnorKSymbol_mul_eq_zero_of_finite (a 0) (a 1)

namespace MilnorKTheory

/-- The actual integral degree-two Milnor group of every finite field is zero. -/
theorem eq_zero_of_finite (z : MilnorKTheory k 2) : z = 0 := by
  have he : (AddMonoidHom.id (MilnorKTheory k 2)) = 0 := by
    apply milnorKTheory_addHom_ext
    intro a
    exact milnorKTupleSymbol_two_eq_zero_of_finite a
  exact DFunLike.congr_fun he z

/-- Native integral Milnor K₂ of a finite field has one element. -/
instance finiteField_two_subsingleton : Subsingleton (MilnorKTheory k 2) :=
  ⟨fun a b => (eq_zero_of_finite a).trans (eq_zero_of_finite b).symm⟩

end MilnorKTheory

attribute [colib_tag "COL-0279",
  colib_ref "Milnor1970" "Section 1, Example 1.5 (Steinberg), p. 321" "clause"
    "Integral degree-two Milnor vanishing for every finite field; higher degrees are not asserted",
  colib_ref "WeibelKBook" "III, Corollary 6.1.1, symbol calculation" "adaptation"
    "The cyclic-unit and Steinberg-relation proof, directly in the native Milnor group",
  colib_ref "quillen"
  "Quillen/Aglib/KTheory/MilnorK/K2/FiniteField.lean, k2_eq_zero_of_finite"
  "adaptation" "All finite fields, including F2 and F3, on native Stacks Milnor K-theory"]
  milnorKSymbol_mul_eq_zero_of_finite milnorKTupleSymbol_two_eq_zero_of_finite
  MilnorKTheory.eq_zero_of_finite MilnorKTheory.finiteField_two_subsingleton
