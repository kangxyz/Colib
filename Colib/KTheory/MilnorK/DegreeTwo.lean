/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.MilnorKDegreeTwo

/-!
# The pair-symbol presentation of Milnor K₂

The tensor relation used by the earlier Motivic/Aglib degree-two presentation is equivalent to
the generator used in Stacks. The comparison retains the class of each ordered tensor.
See Stacks Project, Tag 0EAY, for the graded Steinberg quotient.
-/

@[expose] public noncomputable section

universe u

open scoped TensorProduct

namespace MilnorK.K2

variable (k : Type u) [Field k]

/-- The two-unit presentation of the Steinberg submodule. This is the relation from
`Aglib.KTheory.MilnorK.K2.Basic` at commit `2c34f185`. -/
def pairSteinbergSpan : Submodule ℤ (TensorProduct ℤ (Additive kˣ) (Additive kˣ)) :=
  Submodule.span ℤ {t | ∃ a b : kˣ, (a : k) + (b : k) = 1 ∧
    t = TensorProduct.tmul ℤ (Additive.ofMul a) (Additive.ofMul b)}

/-- The two-unit relations and the one-parameter Stacks relations generate the same submodule. -/
theorem pairSteinbergSpan_eq : pairSteinbergSpan k = milnorKTwoSteinbergSubmodule k := by
  unfold pairSteinbergSpan milnorKTwoSteinbergSubmodule
  congr 1
  ext t
  constructor
  · rintro ⟨a, b, hab, rfl⟩
    have h₁ : (a : k) ≠ 1 := by
      intro ha
      simp [ha] at hab
    refine ⟨⟨a, a.ne_zero, h₁⟩, ?_⟩
    have ha : Units.mk0 (a : k) a.ne_zero = a := Units.ext rfl
    have hb : Units.mk0 (1 - (a : k)) (sub_ne_zero.mpr h₁.symm) = b := by
      apply Units.ext
      exact (eq_sub_of_add_eq' hab).symm
    simp only [ha, hb]
  · rintro ⟨x, rfl⟩
    exact ⟨Units.mk0 x.1 x.2.1, Units.mk0 (1 - x.1) (sub_ne_zero.mpr x.2.2.symm),
      add_sub_cancel x.1 1, rfl⟩

/-- The canonical Stacks Milnor group agrees with the ordered pair-symbol tensor quotient. -/
def pairPresentationEquiv :
    MilnorKTheory k 2 ≃ₗ[ℤ]
      (TensorProduct ℤ (Additive kˣ) (Additive kˣ) ⧸ pairSteinbergSpan k) :=
  (milnorKTwoEquivTensorProductQuotient k).trans
    (Submodule.quotEquivOfEq _ _ (pairSteinbergSpan_eq k).symm)

/-- The comparison retains each ordered tensor class, and in particular each ordered pair
symbol. -/
@[simp] theorem pairPresentationEquiv_toKGroup
    (t : TensorProduct ℤ (Additive kˣ) (Additive kˣ)) :
    pairPresentationEquiv k (milnorKTwoToKGroup k t) = Submodule.Quotient.mk t := by
  change (Submodule.quotEquivOfEq _ _ (pairSteinbergSpan_eq k).symm)
    (milnorKTwoEquivTensorProductQuotient k (milnorKTwoToKGroup k t)) = _
  rw [milnorKTwoEquivTensorProductQuotient_toKGroup]
  rfl

end MilnorK.K2
