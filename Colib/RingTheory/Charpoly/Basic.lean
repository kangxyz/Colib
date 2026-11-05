/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
# Multiplication characteristic polynomials and their field powers

Evaluation is first identified with the determinant norm over any finite free
commutative algebra. In a finite field extension the characteristic polynomial
of actual multiplication by an element is a power
of its minimal polynomial. The exponent is the degree over its actual simple
intermediate field. The proof compares evaluations via the transitivity of norm.

## Source provenance

Adapted from `Aglib/FieldTheory/FieldCharpolyPower.lean` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`, SHA-256
`e737f131c4bcc5ae458a4e4c7c61eb2da9755ee5dca2fceddca2ff6a499d01dd`. The original module is
`Motivic.Aglib.FieldTheory.FieldCharpolyPower`, source SHA-256
`e737f131c4bcc5ae458a4e4c7c61eb2da9755ee5dca2fceddca2ff6a499d01dd`,
as recorded in the migration manifest.

The generic finite-free evaluation lemma is moved here from
`Aglib/RingTheory/DVRCharpolyResidue.lean`; the field-only entry point delegates
to that same proof. No multiplication, norm, or intermediate-field model is added.
-/

@[expose] public noncomputable section

namespace Algebra

/-- Evaluating the original multiplication characteristic polynomial is the
norm of the literal scalar translate, with no separability assumption. -/
@[colib_tag "COL-0202"]
theorem eval_charpoly_lmul_eq_norm
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Free R S] [Module.Finite R S] (b : S) (r : R) :
    (Algebra.lmul R S b).charpoly.eval r =
      Algebra.norm R (algebraMap R S r - b) := by
  rw [LinearMap.eval_charpoly, Algebra.norm_apply]
  congr 1
  ext x
  change r • x - b * x = (algebraMap R S r - b) * x
  rw [Algebra.smul_def, sub_mul]

variable {k L : Type*} [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L]

/-- Evaluation of the characteristic polynomial of multiplication is a norm. -/
@[colib_tag "COL-0202"]
theorem eval_charpoly_lmul (a : L) (t : k) :
    (lmul k L a).charpoly.eval t = norm k (algebraMap k L t - a) :=
  eval_charpoly_lmul_eq_norm a t

/-- Multiplication by the generator on its simple intermediate field has the
original element's minimal polynomial as its characteristic polynomial. -/
@[colib_tag "COL-0202"]
theorem charpoly_lmul_adjoin_gen (a : L) :
    (lmul k (IntermediateField.adjoin k {a})
      (IntermediateField.AdjoinSimple.gen k a)).charpoly = minpoly k a := by
  let b := IntermediateField.adjoin.powerBasis (Algebra.IsIntegral.isIntegral (R := k) a)
  rw [← LinearMap.charpoly_toMatrix _ b.basis]
  change (leftMulMatrix b.basis b.gen).charpoly = minpoly k a
  rw [charpoly_leftMulMatrix, IntermediateField.adjoin.powerBasis_gen,
    IntermediateField.minpoly_gen]

/-- The actual multiplication characteristic polynomial over an infinite base
field is the minimal polynomial raised to the relative extension degree. -/
@[colib_tag "COL-0202",
  colib_ref "aglib_principal_euler_pin" "FieldTheory/FieldCharpolyPower.lean:27-63"
    "adaptation" "Actual multiplication and simple intermediate fields over an infinite base"]
theorem charpoly_lmul_eq_minpoly_pow [Infinite k] (a : L) :
    (lmul k L a).charpoly =
      (minpoly k a) ^ Module.finrank (IntermediateField.adjoin k {a}) L := by
  let F := IntermediateField.adjoin k {a}
  let x : F := IntermediateField.AdjoinSimple.gen k a
  have heval (t : k) :
      (lmul k L a).charpoly.eval t =
        ((minpoly k a) ^ Module.finrank F L).eval t := by
    rw [eval_charpoly_lmul, Polynomial.eval_pow]
    have hmap : algebraMap F L (algebraMap k F t - x) = algebraMap k L t - a := by
      simp [x]
    rw [← hmap, ← norm_norm (R := k) (S := F), Algebra.norm_algebraMap, map_pow]
    congr 1
    rw [← eval_charpoly_lmul, charpoly_lmul_adjoin_gen]
  exact Polynomial.funext heval

end Algebra
