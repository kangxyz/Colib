/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.FiniteMixedGeneration
import Mathlib.Algebra.Field.ZMod

/-!
# The complete same-field finite mixed-generation chain

The tests retain the literal product splitting field, coefficient polynomial,
native factor map, finite expansion, and original degree. Perfectness is a
construction hypothesis, not a condition on the lower symbol lemmas.
-/

noncomputable section

namespace ColibTest.FiniteMixedGeneration

open Polynomial IntermediateField Stacks.Chow

universe u

variable {k : Type u} [Field k]

/-- The complete chain preserves the original polynomial degree and gives
an explicit signed expansion in that very image's native root field. -/
theorem same_field_degree_and_expansion [PerfectField k]
    (p : k[X]) (hp : p.Monic) [Fact (Irreducible p)] (hprime : p.natDegree.Prime)
    (m : ℕ) (x : MilnorKTheory (AdjoinRoot p) (m + 1)) :
    ∃ s : Finset k[X],
      (∀ r ∈ s, r ≠ 0 ∧ r.natDegree < p.natDegree) ∧
      ∃ S : IntermediateField k (∏ r ∈ s, r).SplittingField,
        FiniteDimensional k S ∧ Algebra.IsSeparable k S ∧
        p.natDegree.Coprime (Module.finrank k S) ∧
        (∀ r ∈ s, (r.map (algebraMap k S)).Splits) ∧
        ∃ hq : Irreducible (p.map (algebraMap k S)),
          let _ : Fact (Irreducible (p.map (algebraMap k S))) := ⟨hq⟩
          (p.map (algebraMap k S)).natDegree = p.natDegree ∧
          ∃ c : ((Fin m → Sˣ) × (AdjoinRoot (p.map (algebraMap k S)))ˣ) →₀ ℤ,
            (c.sum fun ab z => z • milnorKTupleSymbol
              (Fin.snoc (Units.map
                (algebraMap S (AdjoinRoot (p.map (algebraMap k S)))).toMonoidHom ∘ ab.1)
                ab.2)) =
              milnorKTheoryMap (AdjoinRoot.map (algebraMap k S) p
                (p.map (algebraMap k S)) dvd_rfl) (m + 1) x := by
  obtain ⟨s, hs, S, hfinite, hseparable, hcop, hsplit, hq, hc⟩ :=
    exists_finite_coprime_milnorK_mixed_expansion p hp hprime m x
  let : Fact (Irreducible (p.map (algebraMap k S))) := ⟨hq⟩
  refine ⟨s, hs, S, hfinite, hseparable, hcop, hsplit, hq, ?_⟩
  dsimp only
  exact ⟨by simp only [Polynomial.natDegree_map], hc⟩

/-- Characteristic zero supplies perfectness but is not an extra condition
on the generic construction. -/
theorem characteristic_zero [CharZero k]
    (p : k[X]) (hp : p.Monic) [Fact (Irreducible p)] (hprime : p.natDegree.Prime)
    (m : ℕ) (x : MilnorKTheory (AdjoinRoot p) (m + 1)) :
    ∃ s : Finset k[X], ∃ S : IntermediateField k (∏ r ∈ s, r).SplittingField,
      FiniteDimensional k S ∧ p.natDegree.Coprime (Module.finrank k S) ∧
      Irreducible (p.map (algebraMap k S)) := by
  obtain ⟨s, _, S, hfinite, _, hcop, _, hq, _⟩ :=
    exists_finite_coprime_milnorK_mixed_expansion p hp hprime m x
  exact ⟨s, S, hfinite, hcop, hq⟩

/-- Positive characteristic remains included by a perfect finite base field. -/
theorem characteristic_two (p : (ZMod 2)[X]) (hp : p.Monic)
    [Fact (Irreducible p)] (hprime : p.natDegree.Prime)
    (m : ℕ) (x : MilnorKTheory (AdjoinRoot p) (m + 1)) :
    ∃ s : Finset (ZMod 2)[X],
      ∃ S : IntermediateField (ZMod 2) (∏ r ∈ s, r).SplittingField,
        FiniteDimensional (ZMod 2) S ∧ Algebra.IsSeparable (ZMod 2) S ∧
        p.natDegree.Coprime (Module.finrank (ZMod 2) S) ∧
        Irreducible (p.map (algebraMap (ZMod 2) S)) := by
  obtain ⟨s, _, S, hfinite, hseparable, hcop, _, hq, _⟩ :=
    exists_finite_coprime_milnorK_mixed_expansion p hp hprime m x
  exact ⟨s, S, hfinite, hseparable, hcop, hq⟩

/-- The mixed-generation endpoint starts in degree one, with an empty base
prefix and an actual finite expansion in extension-field units. -/
theorem degree_one [PerfectField k]
    (p : k[X]) (hp : p.Monic) [Fact (Irreducible p)] (hprime : p.natDegree.Prime)
    (x : MilnorKTheory (AdjoinRoot p) 1) :
    ∃ s : Finset k[X],
      ∃ S : IntermediateField k (∏ r ∈ s, r).SplittingField,
        FiniteDimensional k S ∧ p.natDegree.Coprime (Module.finrank k S) ∧
        ∃ hq : Irreducible (p.map (algebraMap k S)),
          let _ : Fact (Irreducible (p.map (algebraMap k S))) := ⟨hq⟩
          ∃ c : ((Fin 0 → Sˣ) × (AdjoinRoot (p.map (algebraMap k S)))ˣ) →₀ ℤ,
            (c.sum fun ab z => z • milnorKTupleSymbol
              (Fin.snoc (Units.map
                (algebraMap S (AdjoinRoot (p.map (algebraMap k S)))).toMonoidHom ∘ ab.1)
                ab.2)) =
              milnorKTheoryMap (AdjoinRoot.map (algebraMap k S) p
                (p.map (algebraMap k S)) dvd_rfl) 1 x := by
  obtain ⟨s, _, S, hfinite, _, hcop, _, hq, hc⟩ :=
    exists_finite_coprime_milnorK_mixed_expansion p hp hprime 0 x
  exact ⟨s, S, hfinite, hcop, hq, hc⟩

end ColibTest.FiniteMixedGeneration
