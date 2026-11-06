/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.FieldTheory.PurelyInseparable.PrimeDegree

/-! Regression consumer of the field-theoretic prime-degree criterion, without norm imports. -/

noncomputable section

open Module

universe u

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

example [FiniteDimensional K L] (hp : Nat.Prime (finrank K L))
    (hsep : ¬ Algebra.IsSeparable K L) : IsPurelyInseparable K L :=
  isPurelyInseparable_of_finrank_prime_of_not_isSeparable hp hsep

end
