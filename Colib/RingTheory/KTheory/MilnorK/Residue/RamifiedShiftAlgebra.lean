/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.MilnorKShift

/-!
# The native shift algebra for ramified restriction

The right-symbol recursion uses only the native two-symbol skew relation, the native square
relation, and the two-torsion of `{-1}`. These identities keep the ramification-unit correction
and the quadratic ramification term; they do not assume that two is invertible.

The scaling calculation adapts `MilnorK.residue_scaling_algebra` in
`Aglib.KTheory.MilnorK.Residue.RamifiedRestriction`, revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`, lines 83–99.
-/

@[expose] public noncomputable section

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k]

private theorem square_sub_zsmul_negOne (e : ℕ) (B : MilnorKRing k) :
    ((e : ℤ) * e - e) • (B * milnorKNegOne k) = 0 := by
  induction e with
  | zero => simp
  | succ e ih =>
    have heq : ((e + 1 : ℕ) : ℤ) * (e + 1 : ℕ) - (e + 1 : ℕ) =
        ((e : ℤ) * e - e) + (e : ℤ) * 2 := by push_cast; ring
    rw [heq, add_zsmul, ih, mul_zsmul, two_smul, mul_milnorKNegOne_add_self,
      zsmul_zero, add_zero]

/-- The angular-component correction is stable under appending a symbol. -/
theorem milnorK_ramified_main_recursion (M B : MilnorKRing k) (a c : kˣ) (v : ℤ) :
    (M + B * milnorKSymbol k c) * (milnorKSymbol k a + v • milnorKSymbol k c) =
      M * milnorKSymbol k a +
        (v • M - B * milnorKSymbol k a + v • (B * milnorKNegOne k)) *
          milnorKSymbol k c := by
  have hskew : milnorKSymbol k c * milnorKSymbol k a =
      -(milnorKSymbol k a * milnorKSymbol k c) :=
    eq_neg_of_add_eq_zero_left (milnorKSymbol_mul_add_mul_comm c a)
  have hself : milnorKSymbol k c * milnorKSymbol k c =
      milnorKNegOne k * milnorKSymbol k c := by
    have h := milnorKSymbol_mul_self_add_mul_negOne (k := k) c
    have ht := mul_milnorKNegOne_add_self (milnorKSymbol k c)
    rw [← milnorKNegOne_mul_comm] at h ht
    exact add_right_cancel (h.trans ht.symm)
  calc
    _ = M * milnorKSymbol k a + v • (M * milnorKSymbol k c) +
        B * (milnorKSymbol k c * milnorKSymbol k a) +
        v • (B * (milnorKSymbol k c * milnorKSymbol k c)) := by
      simp only [mul_add, add_mul, mul_smul_comm, mul_assoc, smul_add]
      abel
    _ = _ := by
      rw [hskew, hself]
      simp only [mul_neg, add_mul, sub_mul, smul_mul_assoc, mul_assoc]
      abel

/-- The quadratic ramification contribution vanishes by the native two-torsion sign relation. -/
theorem milnorK_ramified_shift_recursion (M B A C : MilnorKRing k) (v : ℤ) (e : ℕ) :
    ((e : ℤ) * v) • (M + B * C) - ((e : ℤ) • B) * (A + v • C) +
        ((e : ℤ) * e * v) • (B * milnorKNegOne k) =
      (e : ℤ) • (v • M - B * A + v • (B * milnorKNegOne k)) := by
  calc
    _ = (e : ℤ) • (v • M - B * A + v • (B * milnorKNegOne k)) +
        v • (((e : ℤ) * e - e) • (B * milnorKNegOne k)) := by
      simp only [mul_add, mul_smul_comm, smul_mul_assoc, smul_add, smul_sub, smul_smul]
      module
    _ = _ := by rw [square_sub_zsmul_negOne, smul_zero, add_zero]

end Stacks.Chow
