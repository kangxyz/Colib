/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.FieldNorm
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# The selected simple presentation of the chosen norm in prime degree

The first non-base element selected by the native `milnorKNormAux` generates a
prime-degree extension. Its remaining tower is bijective, so unfolding the actual
definition identifies the chosen norm with that selected simple presentation.

No perfectness, normality, separability, presentation independence, or general
norm tower law is used. Both fields have the universe required by the native norm.
There is no new norm, carrier, or comparison structure.

-/

@[expose] public noncomputable section

open Polynomial Module IntermediateField

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

omit [FiniteDimensional K L] in
/-- A prime-degree extension has an element outside the actual base-field image. -/
theorem exists_not_mem_range_algebraMap_of_finrank_prime
    (hp : Nat.Prime (finrank K L)) :
    ∃ a : L, a ∉ Set.range (algebraMap K L) := by
  classical
  by_contra h
  have hb : Function.Bijective (algebraMap K L) := bijective_algebraMap_of_forall h
  have hdim : finrank K L = 1 := by
    rw [← (AlgEquiv.ofBijective (Algebra.ofId K L) hb).toLinearEquiv.finrank_eq,
      finrank_self]
  exact hp.ne_one hdim

omit [FiniteDimensional K L] in
/-- Every non-base element generates an actual prime-degree extension. -/
theorem adjoin_simple_eq_top_of_finrank_prime
    (hp : Nat.Prime (finrank K L)) {a : L}
    (ha : a ∉ Set.range (algebraMap K L)) : K⟮a⟯ = ⊤ := by
  let : IsSimpleOrder (IntermediateField K L) :=
    IntermediateField.isSimpleOrder_of_finrank_prime K L hp
  rcases IsSimpleOrder.eq_bot_or_eq_top K⟮a⟯ with hbot | htop
  · exact False.elim (ha (IntermediateField.mem_bot.mp
      (adjoin_simple_eq_bot_iff.mp hbot)))
  · exact htop

omit [FiniteDimensional K L] in
/-- The inclusion of the selected simple intermediate field is bijective in prime degree. -/
theorem bijective_algebraMap_adjoin_simple_of_finrank_prime
    (hp : Nat.Prime (finrank K L)) {a : L}
    (ha : a ∉ Set.range (algebraMap K L)) :
    Function.Bijective (algebraMap K⟮a⟯ L) := by
  refine ⟨(algebraMap K⟮a⟯ L).injective, ?_⟩
  intro b
  have hb : b ∈ K⟮a⟯ := by
    rw [adjoin_simple_eq_top_of_finrank_prime hp ha]
    exact IntermediateField.mem_top
  exact ⟨⟨b, hb⟩, rfl⟩

/-- Unfolding the chosen tower in prime degree leaves its selected simple norm and
the inverse of the actual intermediate-field inclusion. The proof `h` selects
exactly the witness used by the native dependent conditional. -/
theorem milnorKNormRing_eq_selected_adjoinSimple_of_prime
    (hp : Nat.Prime (finrank K L))
    (h : ∃ a : L, a ∉ Set.range (algebraMap K L)) :
    milnorKNormRing K L =
      (milnorKNormAdjoinSimple K (Algebra.IsIntegral.isIntegral (R := K) h.choose)).comp
        (milnorKRingMap
          ((RingEquiv.ofBijective (algebraMap K⟮h.choose⟯ L)
            (bijective_algebraMap_adjoin_simple_of_finrank_prime hp h.choose_spec)).symm :
              L →+* K⟮h.choose⟯)).toAddMonoidHom := by
  classical
  rw [milnorKNormRing, milnorKNormAux, dite_eq_left h]
  change
    (milnorKNormAdjoinSimple K (Algebra.IsIntegral.isIntegral (R := K) h.choose)).comp
        (milnorKNormRing K⟮h.choose⟯ L) = _
  ext x
  exact congrArg
    (milnorKNormAdjoinSimple K (Algebra.IsIntegral.isIntegral (R := K) h.choose))
    (milnorKNormRing_of_bijective
      (bijective_algebraMap_adjoin_simple_of_finrank_prime hp h.choose_spec) x)

/-- The actual chosen norm admits its own selected minpoly presentation in prime degree.
The polynomial degree is the actual extension degree. This does not compare an arbitrary
user-supplied presentation with the selected presentation. -/
theorem exists_selected_simpleMilnorNorm_presentation_of_prime
    (hp : Nat.Prime (finrank K L)) :
    ∃ (a : L) (_ha : a ∉ Set.range (algebraMap K L)),
      ∃ e : L ≃ₐ[K]
          (K[X] ⧸ Ideal.span
            {poly (minpolyOfDegree K (Algebra.IsIntegral.isIntegral (R := K) a))}),
        (minpoly K a).natDegree = finrank K L ∧
          ∀ x : MilnorKRing L,
            milnorKNormRing K L x =
              simpleMilnorNorm
                (minpolyOfDegree K (Algebra.IsIntegral.isIntegral (R := K) a))
                (milnorKRingMap e.toRingHom x) := by
  classical
  have h : ∃ a : L, a ∉ Set.range (algebraMap K L) :=
    exists_not_mem_range_algebraMap_of_finrank_prime hp
  let a : L := h.choose
  have ha : a ∉ Set.range (algebraMap K L) := h.choose_spec
  have hi : IsIntegral K a := Algebra.IsIntegral.isIntegral (R := K) a
  have hb : Function.Bijective (algebraMap K⟮a⟯ L) :=
    bijective_algebraMap_adjoin_simple_of_finrank_prime hp ha
  let g : K⟮a⟯ ≃ₐ[K] L := AlgEquiv.ofBijective (IntermediateField.val K⟮a⟯) hb
  let e : L ≃ₐ[K] (K[X] ⧸ Ideal.span {poly (minpolyOfDegree K hi)}) :=
    g.symm.trans (adjoinSimpleEquivQuot K hi)
  have hdim : (minpoly K a).natDegree = finrank K L :=
    (IntermediateField.adjoin.finrank hi).symm.trans g.toLinearEquiv.finrank_eq
  refine ⟨a, ha, e, hdim, ?_⟩
  intro x
  have hchosen := congrArg (fun N : MilnorKRing L →+ MilnorKRing K => N x)
    (milnorKNormRing_eq_selected_adjoinSimple_of_prime hp h)
  change milnorKNormRing K L x =
    simpleMilnorNorm (minpolyOfDegree K hi)
      (milnorKRingMap (adjoinSimpleEquivQuot K hi).toRingEquiv.toRingHom
        (milnorKRingMap
          ((RingEquiv.ofBijective (algebraMap K⟮a⟯ L) hb).symm : L →+* K⟮a⟯) x))
    at hchosen
  rw [milnorKRingMap_comp_apply] at hchosen
  exact hchosen

end Stacks.Chow

end
