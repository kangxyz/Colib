/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.MilnorK.FiniteMixedWitnesses

/-!
# Native representatives, split evaluation and classwise finite witnesses

The lower statements have independent field universes and no perfectness,
separability, prime-degree or finite-extension premise. The index tests keep
strict source bounds distinct from the native weak filtration bounds.
-/

noncomputable section

namespace ColibTest.FiniteMixedWitnesses

open Polynomial Stacks.Chow

universe u v

variable {k : Type u} [Field k]

/-- A strict source bound is shifted by one relative to a native weak bound. -/
theorem strict_weak_degree_offset (r : k[X]) (d : ℕ) :
    r.natDegree < d + 1 ↔ r.natDegree ≤ d := by
  omega

/-- Strict degree below two is exactly the native weak linear bound. -/
theorem linear_bound_offset (r : k[X]) : r.natDegree < 2 ↔ r.natDegree ≤ 1 := by
  omega

/-- A linear rational unit lies in native filtration bound one, not a copied
source stage indexed by two. -/
theorem native_linear_bound (a : k) :
    polyUnit (X_sub_C_ne_zero a) ∈ polyUnitsOfDegreeLE k 1 :=
  polyUnit_mem_polyUnitsOfDegreeLE (X_sub_C_ne_zero a) (by simp)

/-- The canonical native representative has the original strict bound and
maps to the literal unit in the same quotient. -/
theorem actual_polyRep (p : k[X]) (hp : p.Monic) [Fact (Irreducible p)]
    (a : (AdjoinRoot p)ˣ) :
    let r := polyRep hp (Fact.out : Irreducible p).ne_one a
    r ≠ 0 ∧ r.natDegree < p.natDegree ∧ AdjoinRoot.mk p r = (a : AdjoinRoot p) := by
  exact ⟨polyRep_ne_zero hp (Fact.out : Irreducible p).ne_one a,
    natDegree_polyRep_lt hp (Fact.out : Irreducible p).ne_one a,
    mk_polyRep hp (Fact.out : Irreducible p).ne_one a⟩

/-- Native homogeneous classes admit finite integer combinations without a
new free-symbol presentation. Degree zero is included in this lower lemma. -/
theorem finite_symbol_sum (n : ℕ) (x : MilnorKTheory k n) :
    ∃ c : (Fin n → kˣ) →₀ ℤ, c.sum (fun a z => z • milnorKTupleSymbol a) = x :=
  exists_finsupp_milnorKTupleSymbol n x

/-- Split evaluation works in an arbitrary coefficient field, including an
independent universe and a nonfinite extension. -/
theorem actual_split_evaluation {E : Type v} [Field E] [Algebra k E]
    (θ : E) (m : ℕ) (a : Fin (m + 1) → k[X])
    (hsplit : ∀ i, (a i).Splits) (hne : ∀ i, aeval θ (a i) ≠ 0) :
    milnorKTupleSymbol (fun i => Units.mk0 (aeval θ (a i)) (hne i)) ∈
      milnorKMixedSpan (algebraMap k E) m :=
  milnorKTupleSymbol_aeval_mem_mixedSpan θ m a hsplit hne

/-- The positive degree-one boundary has an empty base-field prefix. -/
theorem empty_prefix {E : Type v} [Field E] [Algebra k E]
    (θ : E) (a : Fin 1 → k[X]) (hsplit : ∀ i, (a i).Splits)
    (hne : ∀ i, aeval θ (a i) ≠ 0) :
    milnorKTupleSymbol (fun i => Units.mk0 (aeval θ (a i)) (hne i)) ∈
      milnorKMixedSpan (algebraMap k E) 0 :=
  milnorKTupleSymbol_aeval_mem_mixedSpan θ 0 a hsplit hne

/-- Repetition retains the native negative-one correction, rather than
asserting that a repeated entry vanishes. No characteristic is excluded. -/
theorem repeated_entry (a : kˣ) :
    milnorKSymbol k a * milnorKSymbol k a =
      -(milnorKSymbol k a * milnorKNegOne k) :=
  eq_neg_of_add_eq_zero_left (milnorKSymbol_mul_self_add_mul_negOne (k := k) a)

/-- The actual coefficient-factor map evaluates the source representative;
no alternative quotient map is inserted. -/
theorem actual_factor_map {L : Type v} [Field L]
    (p : k[X]) (hp : p.Monic) [Fact (Irreducible p)]
    (φ : k →+* L) (q : L[X]) [Fact (Irreducible q)] (hq : q ∣ p.map φ)
    (a : (AdjoinRoot p)ˣ) :
    aeval (AdjoinRoot.root q)
        ((polyRep hp (Fact.out : Irreducible p).ne_one a).map φ) =
      AdjoinRoot.map φ p q hq (a : AdjoinRoot p) :=
  aeval_map_polyRep_eq_adjoinRoot_map p hp φ q hq a

/-- The target factor need not be monic and its degree need not be prime. -/
theorem nonmonic_factor_allowed {L : Type v} [Field L]
    (p : k[X]) (hp : p.Monic) [Fact (Irreducible p)]
    (φ : k →+* L) (q : L[X]) [Fact (Irreducible q)] (hq : q ∣ p.map φ)
    (m : ℕ) (a : Fin (m + 1) → (AdjoinRoot p)ˣ)
    (hsplit : ∀ i,
      ((polyRep hp (Fact.out : Irreducible p).ne_one (a i)).map φ).Splits) :
    milnorKTheoryMap (AdjoinRoot.map φ p q hq) (m + 1) (milnorKTupleSymbol a) ∈
      milnorKMixedSpan (algebraMap L (AdjoinRoot q)) m :=
  restricted_milnorKTupleSymbol_mem_mixedSpan_of_polyRep_splits p hp φ q hq m a hsplit

/-- One finite witness family is selected before every coefficient field and
actual factor, rather than selecting witnesses separately for each field. -/
theorem witnesses_precede_fields (p : k[X]) (hp : p.Monic) [Fact (Irreducible p)]
    (m : ℕ) (x : MilnorKTheory (AdjoinRoot p) (m + 1)) :
    ∃ s : Finset k[X],
      (∀ r ∈ s, r ≠ 0 ∧ r.natDegree < p.natDegree) ∧
      ∀ (L : Type v) [Field L] (φ : k →+* L) (q : L[X]) [Fact (Irreducible q)]
        (hq : q ∣ p.map φ),
        (∀ r ∈ s, (r.map φ).Splits) →
        milnorKTheoryMap (AdjoinRoot.map φ p q hq) (m + 1) x ∈
          milnorKMixedSpan (algebraMap L (AdjoinRoot q)) m :=
  exists_finite_milnorK_mixed_splitting_witness.{u, v} p hp m x

/-- Span membership supplies coefficients for literal base tuples and one
final extension unit, not only an abstract generation proposition. -/
theorem actual_signed_expansion {E : Type v} [Field E]
    (φ : k →+* E) (m : ℕ) (x : MilnorKTheory E (m + 1))
    (hx : x ∈ milnorKMixedSpan φ m) :
    ∃ c : ((Fin m → kˣ) × Eˣ) →₀ ℤ,
      (c.sum fun ab z => z • milnorKTupleSymbol
        (Fin.snoc (Units.map φ.toMonoidHom ∘ ab.1) ab.2)) = x :=
  milnorKMixedSpan_exists_finsupp φ m x hx

end ColibTest.FiniteMixedWitnesses
