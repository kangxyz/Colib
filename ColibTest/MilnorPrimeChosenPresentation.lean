/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.MilnorK.Norm.PrimeChosenPresentation

/-!
Uncompiled consumers of the selected prime-degree chosen-norm presentation.
No perfectness, normality, or separability instance is present in these consumers.
-/

noncomputable section

open Polynomial Module IntermediateField Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

universe u

attribute [local instance] Ideal.Quotient.field

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

example (hp : Nat.Prime (finrank K L)) :
    ∃ a : L, a ∉ Set.range (algebraMap K L) :=
  exists_not_mem_range_algebraMap_of_finrank_prime hp

example (hp : Nat.Prime (finrank K L)) {a : L}
    (ha : a ∉ Set.range (algebraMap K L)) : K⟮a⟯ = ⊤ :=
  adjoin_simple_eq_top_of_finrank_prime hp ha

example (hp : Nat.Prime (finrank K L)) {a : L}
    (ha : a ∉ Set.range (algebraMap K L)) :
    Function.Bijective (algebraMap K⟮a⟯ L) :=
  bijective_algebraMap_adjoin_simple_of_finrank_prime hp ha

example (hp : Nat.Prime (finrank K L))
    (h : ∃ a : L, a ∉ Set.range (algebraMap K L)) :
    milnorKNormRing K L =
      (milnorKNormAdjoinSimple K (Algebra.IsIntegral.isIntegral (R := K) h.choose)).comp
        (milnorKRingMap
          ((RingEquiv.ofBijective (algebraMap K⟮h.choose⟯ L)
            (bijective_algebraMap_adjoin_simple_of_finrank_prime hp h.choose_spec)).symm :
              L →+* K⟮h.choose⟯)).toAddMonoidHom :=
  milnorKNormRing_eq_selected_adjoinSimple_of_prime hp h

example (hp : Nat.Prime (finrank K L)) :
    ∃ (a : L) (_ha : a ∉ Set.range (algebraMap K L)),
      ∃ e : L ≃ₐ[K]
          (K[X] ⧸ Ideal.span
            {poly (minpolyOfDegree K (Algebra.IsIntegral.isIntegral (R := K) a))}),
        (minpoly K a).natDegree = finrank K L ∧
          ∀ x : MilnorKRing L,
            milnorKNormRing K L x =
              simpleMilnorNorm
                (minpolyOfDegree K (Algebra.IsIntegral.isIntegral (R := K) a))
                (milnorKRingMap e.toRingHom x) :=
  exists_selected_simpleMilnorNorm_presentation_of_prime hp

end
