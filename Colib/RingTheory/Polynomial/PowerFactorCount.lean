/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Squarefree.Basic

/-!
# Exact multiplicities in a product of irreducible polynomial powers

Counting the actual normalized factors extracts the full exponent above each
literal monic irreducible branch. This elementary unique-factorization step is
used after the characteristic-polynomial product identity has been proved.

## Source provenance

Adapted from `Aglib/RingTheory/PolynomialPowerFactorCount.lean` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`, SHA-256
`032cedec6e97b67bb0ccc42893d9e89106a539095a0edbfcfaaebbdff37202aa`. The original module is
`Motivic.Aglib.RingTheory.PolynomialPowerFactorCount`, source SHA-256
`55bf93aead8994e62fd83a00f93e9cddea70d66e2818524959b4f79093275c8b`,
as recorded in the migration manifest.

The former nested branch subtype is replaced by the literal polynomial and its
monicity, irreducibility, and divisibility proofs. The unique-factorization
argument is unchanged and no branch representation is introduced.
-/

@[expose] public noncomputable section

open UniqueFactorizationMonoid

namespace Polynomial

variable {k ι : Type*} [Field k] [DecidableEq k]

/-- Count the multiplicity of a literal polynomial in a finite product of
monic irreducible powers. -/
@[colib_tag "COL-0206"]
theorem count_normalizedFactors_prod_irreducible_pow
    (s : Finset ι) (p : ι → k[X]) (hp : ∀ i, (p i).Monic ∧ Irreducible (p i))
    (w : ι → ℕ) (q : k[X]) :
    (normalizedFactors (∏ i ∈ s, p i ^ w i)).count q =
      ∑ i ∈ s, if p i = q then w i else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      normalizedFactors_mul (pow_ne_zero _ (hp a).2.ne_zero)
        (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hp i).2.ne_zero),
      Multiset.count_add, ih, (hp a).2.normalizedFactors_pow,
      (hp a).1.normalize_eq_self, Multiset.count_replicate]

/-- A squarefree polynomial has each original branch exactly once, so a
product equal to its `e`-th power has total branch exponent exactly `e`. -/
@[colib_tag "COL-0206",
  colib_ref "aglib_principal_euler_pin" "RingTheory/PolynomialPowerFactorCount.lean:29-64"
    "adaptation" "Normalized factors with a literal polynomial and three proof arguments"]
theorem sum_weights_eq_of_prod_eq_squarefree_pow
    [Fintype ι] (P : k[X]) (hP : P.Monic) (hPsq : Squarefree P)
    (p : ι → k[X]) (hp : ∀ i, (p i).Monic ∧ Irreducible (p i))
    (w : ι → ℕ) (e : ℕ) (hprod : ∏ i, p i ^ w i = P ^ e)
    (q : k[X]) (hq : q.Monic) (hqirr : Irreducible q) (hqdvd : q ∣ P) :
    (∑ i, if p i = q then w i else 0) = e := by
  classical
  have hc := congrArg (fun f : k[X] => (normalizedFactors f).count q) hprod
  rw [count_normalizedFactors_prod_irreducible_pow Finset.univ p hp w,
    normalizedFactors_pow, Multiset.count_nsmul] at hc
  have hqmem : q ∈ normalizedFactors P :=
    (Polynomial.mem_normalizedFactors_iff hP.ne_zero).mpr
      ⟨hqirr, hq, hqdvd⟩
  have hcount : (normalizedFactors P).count q = 1 :=
    Multiset.count_eq_one_of_mem
      ((squarefree_iff_nodup_normalizedFactors hP.ne_zero).mp hPsq) hqmem
  simpa only [hcount, mul_one] using hc

end Polynomial
