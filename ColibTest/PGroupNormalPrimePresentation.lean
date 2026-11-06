/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.FieldTheory.PGroupNormalPrimePresentation
import Colib.FieldTheory.Polynomial.PrimeNormal

/-!
# The complete normal prime presentation and scalar-factor chain

One literal polynomial is constructed inside the original field `H` before
any coefficient extension is supplied. Every coefficient field and every
literal irreducible divisor then use that same polynomial and the native
`AdjoinRoot` field. No branch enumeration or substitute field model is used.
-/

noncomputable section

namespace ColibTest.PGroupNormalPrimePresentation

open Polynomial

universe u v w z

variable {k : Type u} {H : Type v} {Ω : Type w} [Field k] [Field H] [Field Ω]
  [Algebra k H] [Algebra k Ω] [FiniteDimensional k H]
  [FiniteDimensional k Ω] [IsGalois k Ω] [CharZero k]

/-- The producer returns a literal polynomial and an algebra embedding into
the original field, not merely into its image in the Galois ambient field. -/
theorem original_field_presentation (p : ℕ) [Fact p.Prime]
    (hG : IsPGroup p (Ω ≃ₐ[k] Ω)) (g : H →ₐ[k] Ω)
    (hH : 1 < Module.finrank k H) :
    ∃ r : k[X], r.Monic ∧ ∃ hr : Irreducible r,
      let _ : Fact (Irreducible r) := ⟨hr⟩
      Normal k (AdjoinRoot r) ∧ r.natDegree = p ∧
        Nonempty (AdjoinRoot r →ₐ[k] H) :=
  Field.exists_normal_prime_presentation_of_isPGroup_embedding p hG g hH

/-- The same polynomial works for every scalar extension in an arbitrary
universe. The actual factor root field is normal and splits the whole mapped
polynomial, and its degree is one or the original specified prime. -/
theorem original_field_all_scalar_extensions (p : ℕ) [Fact p.Prime]
    (hG : IsPGroup p (Ω ≃ₐ[k] Ω)) (g : H →ₐ[k] Ω)
    (hH : 1 < Module.finrank k H) :
    ∃ r : k[X], r.Monic ∧ ∃ hr : Irreducible r,
      let _ : Fact (Irreducible r) := ⟨hr⟩
      Normal k (AdjoinRoot r) ∧ r.natDegree = p ∧
        Nonempty (AdjoinRoot r →ₐ[k] H) ∧
        ∀ (K : Type z) [Field K] [Algebra k K],
          (Irreducible (r.map (algebraMap k K)) ∨ (r.map (algebraMap k K)).Splits) ∧
          ∀ (q : K[X]) (hq : Irreducible q), q ∣ r.map (algebraMap k K) →
            let _ : Fact (Irreducible q) := ⟨hq⟩
            IsSplittingField K (AdjoinRoot q) (r.map (algebraMap k K)) ∧
              Normal K (AdjoinRoot q) ∧ (q.natDegree = 1 ∨ q.natDegree = p) := by
  obtain ⟨r, hrm, hri, hnormal, hdegree, hg⟩ :=
    Field.exists_normal_prime_presentation_of_isPGroup_embedding p hG g hH
  let : Fact (Irreducible r) := ⟨hri⟩
  let : Normal k (AdjoinRoot r) := hnormal
  have hprime : r.natDegree.Prime := by
    simpa only [hdegree] using (Fact.out : p.Prime)
  refine ⟨r, hrm, hri, hnormal, hdegree, hg, ?_⟩
  intro K _ _
  refine ⟨hrm.irreducible_map_or_splits_of_prime_normal hri hprime, ?_⟩
  intro q hq hd
  let : Fact (Irreducible q) := ⟨hq⟩
  let hsplit : IsSplittingField K (AdjoinRoot q) (r.map (algebraMap k K)) :=
    AdjoinRoot.isSplittingField_of_dvd_map hrm hd
  let : IsSplittingField K (AdjoinRoot q) (r.map (algebraMap k K)) := hsplit
  refine ⟨hsplit, Normal.of_isSplittingField (r.map (algebraMap k K)), ?_⟩
  simpa only [hdegree] using
    natDegree_eq_one_or_eq_of_dvd_map_of_prime_normal hrm hri hprime hq hd

end ColibTest.PGroupNormalPrimePresentation
