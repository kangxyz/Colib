/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.FieldTheory.Polynomial.PrimeNormal

/-! # Consumers of the prime-normal scalar dichotomy -/

noncomputable section

namespace ColibTest.PrimeNormal

open Polynomial

universe u v

variable {F : Type u} {K : Type v} [Field F] [Field K] [Algebra F K] [CharZero F]
  {p : F[X]} (hp : p.Monic) (hi : Irreducible p) [Fact (Irreducible p)]
  [Normal F (AdjoinRoot p)] (hprime : p.natDegree.Prime)

include hp hi hprime

/-- The target field can have a different universe and need not be finite
over the base field. -/
theorem arbitrary_extension :
    Irreducible (p.map (algebraMap F K)) ∨ (p.map (algebraMap F K)).Splits :=
  hp.irreducible_map_or_splits_of_prime_normal hi hprime

/-- Reducibility implies complete splitting, not merely existence of a root. -/
theorem reducible_splits (h : ¬Irreducible (p.map (algebraMap F K))) :
    (p.map (algebraMap F K)).Splits :=
  (hp.irreducible_map_or_splits_of_prime_normal hi hprime).resolve_left h

/-- Failure of complete splitting forces irreducibility of the whole image. -/
theorem nonsplit_irreducible (h : ¬(p.map (algebraMap F K)).Splits) :
    Irreducible (p.map (algebraMap F K)) :=
  (hp.irreducible_map_or_splits_of_prime_normal hi hprime).resolve_right h

/-- The degree alternative applies to a literal irreducible divisor without
a monicity assumption on that divisor. -/
theorem actual_factor_degree {q : K[X]} (hq : Irreducible q)
    (hd : q ∣ p.map (algebraMap F K)) :
    q.natDegree = 1 ∨ q.natDegree = p.natDegree :=
  natDegree_eq_one_or_eq_of_dvd_map_of_prime_normal hp hi hprime hq hd

/-- Literal polynomial equality in the nonsplit branch uses the factor's
monicity; degree equality alone does not normalize the leading coefficient. -/
theorem monic_factor_eq_of_nonsplit {q : K[X]} (hqm : q.Monic) (hqi : Irreducible q)
    (hd : q ∣ p.map (algebraMap F K)) (hs : ¬(p.map (algebraMap F K)).Splits) :
    q = p.map (algebraMap F K) := by
  have hmap := (hp.irreducible_map_or_splits_of_prime_normal hi hprime).resolve_right hs
  exact eq_of_monic_of_associated hqm (hp.map _) (hqi.associated_of_dvd hmap hd)

omit hp hprime [CharZero F] [Fact (Irreducible p)] [Normal F (AdjoinRoot p)] in
/-- The scalar image over the base field itself is the original irreducible
polynomial, so its irreducible divisors have the original degree. -/
theorem base_field_factor_degree {q : F[X]} (hq : Irreducible q)
    (hd : q ∣ p.map (algebraMap F F)) : q.natDegree = p.natDegree := by
  have hd' : q ∣ p := by simpa using hd
  exact natDegree_eq_of_degree_eq (degree_eq_degree_of_associated (hq.associated_of_dvd hi hd'))

end ColibTest.PrimeNormal
