/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Cofinality.Grading
public import Colib.CategoryTheory.Waldhausen.FunctorialFactorization.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic

/-! # Actual representability of grading values as a subgroup

Coproduct pushouts realize sums of object grades. A genuine source
cofibration/weak factorization of the map to zero, followed by its actual
cofiber pushout, realizes the negative grade. Thus the actual object-grade
range is a subgroup, without a K-zero presentation or an arbitrary tuple
realizability hypothesis.

Implementation provenance: `Quillen/Waldhausen/Cofinality/GradingRange.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
maps, hypotheses and independent object/hom universes are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v w
namespace CategoryTheory.Waldhausen.Cofinality.Grading
variable {C : Type u} [Category.{v} C] {G : Type w} [AddCommGroup G]
  {W : Structure C} (d : Grading W G)

/-- The actual endpoint coproduct realizes the sum of the original object grades. -/
theorem exists_value_add (A B : C) : ∃ Q : C, d.value Q = d.value A + d.value B := by
  obtain ⟨Q, i, j, hQ⟩ := W.pushout_exists (W.isZero.to_ A) (W.isZero.to_ B) (W.cof_zero A)
  refine ⟨Q, ?_⟩
  rw [d.pushout (W.cof_zero A) hQ, d.zero, sub_zero]

variable (T : FunctorialFactorization W)

include T in
/-- The actual cofiber of a genuine factorization to zero realizes the negative grade. -/
theorem exists_value_neg (A : C) : ∃ Q : C, d.value Q = - d.value A := by
  let f := Arrow.mk (W.isZero.from_ A)
  have hm : d.value (T.middle.obj f) = 0 :=
    (d.weak (T.projection.app f) (T.weak f)).trans d.zero
  obtain ⟨Q, q, j, hQ⟩ := W.pushout_exists (T.inclusion.app f) (W.isZero.from_ A) (T.cofibration f)
  refine ⟨Q, ?_⟩
  rw [d.pushout (T.cofibration f) hQ, hm, d.zero, zero_add, zero_sub]
  rfl

/-- The actual range of the original object grading is a subgroup, with no enlargement. -/
def valueRange : AddSubgroup G where
  carrier := Set.range d.value
  zero_mem' := ⟨W.zero, d.zero⟩
  add_mem' := by
    rintro a b ⟨A, rfl⟩ ⟨B, rfl⟩
    exact d.exists_value_add A B
  neg_mem' := by
    rintro a ⟨A, rfl⟩
    exact d.exists_value_neg T A

/-- The original object value, regarded as an element of its actual range. -/
def valueToRange (A : C) : d.valueRange T := ⟨d.value A, ⟨A, rfl⟩⟩

/-- Every subgroup element has an actual original object representative. -/
theorem valueToRange_surjective : Function.Surjective (d.valueToRange T) := by
  rintro ⟨_, A, rfl⟩
  exact ⟨A, rfl⟩

/-- The honest surjective range-valued grading retains all original additive equations. -/
def rangeGrading : Grading W (d.valueRange T) where
  value := d.valueToRange T
  zero := Subtype.ext d.zero
  weak f hf := Subtype.ext (d.weak f hf)
  pushout hi hQ := Subtype.ext (d.pushout hi hQ)

/-- Forgetting range membership recovers the actual original grading value. -/
@[simp] theorem rangeGrading_value_coe (A : C) :
    ((d.rangeGrading T).value A : G) = d.value A := rfl

/-- Passage to the exact value range preserves the entire actual coarse weak class. -/
theorem rangeGrading_weak_iff {A B : C} (f : A ⟶ B) :
    (d.rangeGrading T).gradeWeak f ↔ d.gradeWeak f := Subtype.ext_iff

/-- The entire coarse Waldhausen structure is unchanged after restricting to the actual range. -/
theorem rangeGrading_coarseStructure : (d.rangeGrading T).coarseStructure = d.coarseStructure := by
  unfold coarseStructure
  congr 1
  funext A B f
  exact propext (d.rangeGrading_weak_iff T f)

end CategoryTheory.Waldhausen.Cofinality.Grading
