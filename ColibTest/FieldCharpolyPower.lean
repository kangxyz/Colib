/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.Charpoly.Basic
import Mathlib.Algebra.CharZero.Infinite

/-! Regression tests for the actual field multiplication characteristic polynomial. -/

noncomputable section

namespace ColibTest.FieldCharpolyPower

/-- Evaluation works over an arbitrary finite free commutative algebra. -/
theorem finite_free_evaluation
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Free R S] [Module.Finite R S] (b : S) (r : R) :
    (Algebra.lmul R S b).charpoly.eval r =
      Algebra.norm R (algebraMap R S r - b) :=
  Algebra.eval_charpoly_lmul_eq_norm b r

variable {k L : Type*} [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L]

/-- Evaluation is the norm of scalar minus the original element. -/
theorem eval_at_scalar (a : L) (t : k) :
    (Algebra.lmul k L a).charpoly.eval t =
      Algebra.norm k (algebraMap k L t - a) :=
  Algebra.eval_charpoly_lmul a t

/-- No infinite-base hypothesis is needed inside the simple extension. -/
theorem simple_generator (a : L) :
    (Algebra.lmul k (IntermediateField.adjoin k {a})
      (IntermediateField.AdjoinSimple.gen k a)).charpoly = minpoly k a :=
  Algebra.charpoly_lmul_adjoin_gen a

/-- The exponent is the actual relative degree over the simple intermediate field. -/
theorem infinite_base [Infinite k] (a : L) :
    (Algebra.lmul k L a).charpoly =
      (minpoly k a) ^ Module.finrank (IntermediateField.adjoin k {a}) L :=
  Algebra.charpoly_lmul_eq_minpoly_pow a

/-- Characteristic-zero consumers obtain the infinite-base theorem. -/
theorem characteristic_zero [CharZero k] (a : L) :
    (Algebra.lmul k L a).charpoly =
      (minpoly k a) ^ Module.finrank (IntermediateField.adjoin k {a}) L :=
  Algebra.charpoly_lmul_eq_minpoly_pow a

end ColibTest.FieldCharpolyPower
