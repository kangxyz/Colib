/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# Inseparability in prime field degree

The separable degree divides the finite field degree. In prime degree, failure of
separability therefore forces separable degree one and hence pure inseparability.
No normality or characteristic assumption is needed. This is a field-theoretic
statement with no Milnor K-theory dependency.

-/

@[expose] public noncomputable section

open Module

universe u

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- A finite prime-degree extension that is not separable is purely inseparable.
Normality is not needed for this degree dichotomy. -/
theorem isPurelyInseparable_of_finrank_prime_of_not_isSeparable
    [FiniteDimensional K L] (hp : Nat.Prime (finrank K L))
    (hsep : ¬ Algebra.IsSeparable K L) : IsPurelyInseparable K L := by
  rcases (Nat.dvd_prime hp).mp (Field.finSepDegree_dvd_finrank K L) with h | h
  · exact isPurelyInseparable_of_finSepDegree_eq_one h
  · exact False.elim (hsep ((Field.finSepDegree_eq_finrank_iff K L).mp h))

end
