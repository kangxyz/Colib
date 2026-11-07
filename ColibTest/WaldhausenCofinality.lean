/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Cofinality.GeneralDense

/-! # Original-map and degree-zero regressions for dense Waldhausen cofinality -/

@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.Cofinality CategoryTheory.Waldhausen.Fibration
universe u v w

namespace ColibTest.WaldhausenCofinality

section Dense
variable {C : Type u} [Category.{v} C] {W : Structure C} [HasBinaryCoproducts C]
  {P : ObjectProperty C} (h : DenseCofiberData W P)
  (D : RowFactorization.JointData (NestedWeakEquivalences.refl W))
  (hs : RowFactorization.SecondEndpointSection (NestedWeakEquivalences.refl W) D)

example (n : ℕ) :
    (↑(h.inclusionKEquivGeneral D hs n) : h.waldhausenStructure.K (n + 1) →* W.K (n + 1)) =
      KMap h.inclusion_exact (n + 1) := rfl

example : h.toZeroGrade ⋙ acyclicInclusion h.grading.nested = P.ι := rfl

example : Function.Injective (KMap h.inclusion_exact 0) ∧
    (KMap h.inclusion_exact 0).range = (KMap (changeWeak_exact h.grading.nested) 0).ker ∧
    Function.Surjective (KMap (changeWeak_exact h.grading.nested) 0) :=
  h.inclusion_KZero_exact_general D hs
end Dense

section Grading
variable {C G : Type u} [Category.{v} C] [AddCommGroup G]
  {W : Structure C} (d : Grading W G)
  (D : RowFactorization.JointData (NestedWeakEquivalences.refl W))
  (hs : RowFactorization.SecondEndpointSection (NestedWeakEquivalences.refl W) D)

example (n : ℕ) :
    (↑(d.zeroGradeKEquivGeneral D hs n) : (acyclicStructure d.nested).K (n + 1) →*
      W.K (n + 1)) = KMap (acyclicInclusion_exact d.nested) (n + 1) := rfl

example (A : AsSmall.{0} C) :
    (d.asSmallGrading.value A).down = d.value (AsSmall.down.obj A) := rfl

example : (d.jointData D).joint = D.joint := rfl
end Grading

section ActualRange
variable {C : Type u} [Category.{v} C] (W : Structure C)

private def zeroGrading : Grading W ℤ where
  value _ := 0
  zero := rfl
  weak _ _ := rfl
  pushout _ _ := by simp

example (T : FunctorialFactorization W) : (zeroGrading W).valueRange T = ⊥ := by
  ext z
  change (∃ X : C, (0 : ℤ) = z) ↔ z = 0
  constructor
  · rintro ⟨_, rfl⟩
    rfl
  · rintro rfl
    exact ⟨W.zero, rfl⟩
end ActualRange

end ColibTest.WaldhausenCofinality
