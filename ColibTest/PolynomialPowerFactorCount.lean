/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.Polynomial.PowerFactorCount
import Mathlib.Data.Fintype.BigOperators

/-!
# Consumers of exact polynomial-power multiplicities

These use the literal polynomial and its proof arguments. Repeated branches,
zero weights, nonmatching factors, and empty products are included; no new
branch wrapper or assumed characteristic-polynomial identity is introduced.
-/

noncomputable section

open Polynomial UniqueFactorizationMonoid

namespace ColibTest.PolynomialPowerFactorCount

variable {k : Type*} [Field k] [DecidableEq k]

/-- Two branches with the same irreducible polynomial contribute both weights. -/
theorem repeated_branches (q : k[X]) (hq : q.Monic) (hqirr : Irreducible q)
    (a b : ℕ) :
    (normalizedFactors (q ^ a * q ^ b)).count q = a + b := by
  classical
  simpa [Fintype.prod_bool, Fintype.sum_bool] using
    Polynomial.count_normalizedFactors_prod_irreducible_pow Finset.univ
      (fun _ : Bool ↦ q) (fun _ ↦ ⟨hq, hqirr⟩) (fun i ↦ cond i a b) q

/-- A present branch with weight zero contributes no factor. -/
theorem zero_weight_branch (q : k[X]) (hq : q.Monic) (hqirr : Irreducible q)
    (b : ℕ) :
    (normalizedFactors (q ^ 0 * q ^ b)).count q = b := by
  simpa using repeated_branches q hq hqirr 0 b

/-- Three matching branches retain the full sum, including the zero weight. -/
theorem three_matching_branches (q : k[X]) (hq : q.Monic) (hqirr : Irreducible q) :
    (normalizedFactors (q ^ 2 * q ^ 0 * q ^ 3)).count q = 5 := by
  simpa using repeated_branches q hq hqirr 2 3

/-- A different irreducible factor does not contribute to the selected branch. -/
theorem distinct_branch_factors (q r : k[X])
    (hq : q.Monic) (hqirr : Irreducible q)
    (hr : r.Monic) (hrirr : Irreducible r) (hne : r ≠ q) (a b : ℕ) :
    (normalizedFactors (q ^ a * r ^ b)).count q = a := by
  classical
  have hp : ∀ i : Bool, (cond i q r).Monic ∧ Irreducible (cond i q r) := by
    intro i
    cases i
    · exact ⟨hr, hrirr⟩
    · exact ⟨hq, hqirr⟩
  simpa [Fintype.prod_bool, Fintype.sum_bool, hne] using
    Polynomial.count_normalizedFactors_prod_irreducible_pow Finset.univ
      (fun i : Bool ↦ cond i q r) hp (fun i ↦ cond i a b) q

/-- The empty index type gives the unit polynomial with multiplicity zero. -/
theorem empty_factor_product (p : PEmpty → k[X]) (w : PEmpty → ℕ) (q : k[X]) :
    (normalizedFactors (∏ i, p i ^ w i)).count q = 0 := by
  simp

/-- Every weight can vanish without any nonempty-index or positive-weight premise. -/
theorem all_zero_weights {ι : Type*} [Fintype ι] (p : ι → k[X]) (q : k[X]) :
    (normalizedFactors (∏ i, p i ^ 0)).count q = 0 := by
  simp

/-- The complete multiplicity extraction accepts a literal monic irreducible divisor. -/
theorem actual_irreducible_divisor {ι : Type*} [Fintype ι]
    (P : k[X]) (hP : P.Monic) (hPsq : Squarefree P)
    (p : ι → k[X]) (hp : ∀ i, (p i).Monic ∧ Irreducible (p i))
    (w : ι → ℕ) (e : ℕ) (hprod : ∏ i, p i ^ w i = P ^ e)
    (q : k[X]) (hq : q.Monic) (hqirr : Irreducible q) (hqdvd : q ∣ P) :
    (∑ i, if p i = q then w i else 0) = e :=
  Polynomial.sum_weights_eq_of_prod_eq_squarefree_pow
    P hP hPsq p hp w e hprod q hq hqirr hqdvd

end ColibTest.PolynomialPowerFactorCount
