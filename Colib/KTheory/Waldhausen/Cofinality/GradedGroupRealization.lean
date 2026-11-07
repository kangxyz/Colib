/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Cofinality.GradedGroupNerve
public import Colib.KTheory.Waldhausen.Cofinality.GradedRealization

/-! # The original graded coarse S-map to its actual value-group nerve

Genuine source factorization makes the original object-grade range an actual
subgroup. Actual finite replacement realizes every nerve chain in this range.
The resulting complete weak comparison retains each original grid coordinate;
neither tuple realizability nor K-zero identification is a premise.

Implementation provenance: `Quillen/Waldhausen/Cofinality/GradedGroupRealization.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
maps, hypotheses and independent object/hom universes are retained.
-/
@[expose] public section

open CategoryTheory.Waldhausen.QuotientRows


noncomputable section
open Topology SSet
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Cofinality.Grading
open QuotientRows
variable {C G : Type u} [SmallCategory C] [AddCommGroup G]
  {W : Structure C} (d : Grading W G) (T : FunctorialFactorization W)

/-- Restricting each actual interval grade to its actual range changes only membership proofs. -/
def rowGradeToRange (n : SimplexCategory) (a : d.RowGrade n) : (d.rangeGrading T).RowGrade n :=
  ⟨fun p ↦ ⟨a.val p, by
      obtain ⟨R, hR⟩ := a.property
      exact ⟨R.obj.obj p, congrFun hR p⟩⟩, by
    obtain ⟨R, hR⟩ := a.property
    let R' : Obj (d.rangeGrading T).coarseStructure n :=
      ⟨R.obj, ⟨R.property.zero, R.property.cofibration, R.property.quotient⟩⟩
    exact ⟨R', funext fun p ↦ Subtype.ext (congrFun hR p)⟩⟩

/-- Forgetting range membership retains the entire actual original quotient diagram. -/
def rowGradeFromRange (n : SimplexCategory) (a : (d.rangeGrading T).RowGrade n) : d.RowGrade n :=
  ⟨fun p ↦ (a.val p : G), by
    obtain ⟨R, hR⟩ := a.property
    let R' : Obj d.coarseStructure n :=
      ⟨R.obj, ⟨R.property.zero, R.property.cofibration, R.property.quotient⟩⟩
    exact ⟨R', funext fun p ↦ congrArg Subtype.val (congrFun hR p)⟩⟩

/-- Original realized row grades and their range-valued versions are the same actual data. -/
def rowGradeRangeEquiv (n : SimplexCategory) : d.RowGrade n ≃ (d.rangeGrading T).RowGrade n where
  toFun := d.rowGradeToRange T n
  invFun := d.rowGradeFromRange T n
  left_inv _ := rfl
  right_inv _ := rfl

/-- Range restriction is strictly compatible with every original simplicial operator. -/
def gradeRangeIso : d.gradeSSet ≅ (d.rangeGrading T).gradeSSet :=
  NatIso.ofComponents (fun n ↦ Equiv.toIso (d.rowGradeRangeEquiv T n.unop)) (by
    intro n m α
    apply ConcreteCategory.hom_ext
    intro a
    apply Subtype.ext
    rfl)

/-- The canonical map from the original coarse S-construction to the actual value-group nerve. -/
def groupGradeMap : sSet d.coarseStructure.cof d.coarseStructure.weq ⟶
    nerve (SingleObj (Multiplicative (d.valueRange T))) :=
  d.gradeMap ≫ (d.gradeRangeIso T).hom ≫
    ((d.rangeGrading T).gradeGroupNerveIso T (d.valueToRange_surjective T)).hom

/-- Actual categorical constructions prove complete weakness of the original group-grading map. -/
@[colib_tag "COL-0267", colib_ref "ThomasonTrobaugh1990"
  "Theorem 1.10.1, pp. 275-277" "adaptation"
  "The original coarse delooping compares weakly with the nerve of its actual \
    object-value subgroup"]
theorem groupGradeMap_isRealizationWeakEquivalence : IsRealizationWeakEquivalence
    (d.groupGradeMap T) := by
  simpa only [IsRealizationWeakEquivalence, groupGradeMap, Functor.map_comp, TopCat.hom_comp,
    ContinuousMap.comp_assoc] using
    (IsRealizationWeakEquivalence.of_isIso
      ((d.rangeGrading T).gradeGroupNerveIso T (d.valueToRange_surjective T)).hom).comp
      ((IsRealizationWeakEquivalence.of_isIso (d.gradeRangeIso T).hom).comp
        d.gradeMap_isRealizationWeakEquivalence)

/-- Every nerve arrow is exactly the grade of the original grid's first row interval. -/
@[simp] theorem groupGradeMap_component (n : SimplexCategory)
    (X : (sSet d.coarseStructure.cof d.coarseStructure.weq).obj (op n)) (p : Interval n) :
    ((@Multiplicative.toAdd (d.valueRange T)
      (((d.groupGradeMap T).app (op n) X).map (homOfLE p.property))) : G) =
      d.value (X.val.obj (0, p)) := rfl

end CategoryTheory.Waldhausen.Cofinality.Grading
