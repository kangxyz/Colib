/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Cofinality.GradedRows
public import Colib.Topology.Realization.BisimplicialWeakEquivalence
public import Colib.Topology.Realization.TwoSidedBar.AugmentationEquivalence

/-! # Original coarse S-realization compared with actual realized row grades

All row comparison homotopies are constructed with actual zero arrows. Their
strict ordinal compatibility and the proved weak diagonal theorem give a
complete weak comparison of the original coarse S-realization with the
simplicial set of genuinely realized row grades. No arbitrary grade tuple,
K-zero presentation, group-space calculation or cofinality endpoint is assumed.

Implementation provenance: `Quillen/Waldhausen/Cofinality/GradedRealization.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
maps, hypotheses and independent object/hom universes are retained.
-/
@[expose] public section

open CategoryTheory.TheoremA
open CategoryTheory.Waldhausen.QuotientRows


noncomputable section
open Topology SSet
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Cofinality.Grading
open QuotientRows TheoremA
variable {C G : Type u} [SmallCategory C] [AddCommGroup G]
  {W : Structure C} (d : Grading W G)

/-- The actual grade simplices, constant only in the nerve direction. -/
def gradeBisimplicial : SimplexCategoryᵒᵖ ⥤ SSet.{u} :=
  d.gradeSSet ⋙ Functor.const SimplexCategoryᵒᵖ

/-- Original weak-row chains map to the grade of their actual first row. -/
def gradeNerveMap : weakRowNerve d.coarseStructure ⟶ d.gradeBisimplicial where
  app n := nerveMap (d.rowProjection n.unop) ≫ (TwoSidedBar.discreteNerveIso (d.RowGrade
    n.unop)).hom
  naturality n m α := by
    ext k F : 4
    rfl

/-- Each actual row comparison has the complete weak property. -/
theorem gradeNerveMap_row_weak (n : ℕ) :
    IsRealizationWeakEquivalence ((d.gradeNerveMap).app (op ⦋n⦌)) := by
  have hp : IsWeakHomotopyEquivalence (classifyingSpaceMap (d.rowProjection ⦋n⦌)).hom := by
    rw [← d.rowProjectionHomotopyEquiv_toFun]
    exact isWeakHomotopyEquivalence_of_homotopyEquiv (d.rowProjectionHomotopyEquiv ⦋n⦌)
  simpa only [IsRealizationWeakEquivalence, gradeNerveMap, Functor.map_comp, TopCat.hom_comp,
    classifyingSpaceMap, ClassifyingSpace, weakRowNerve, weakRowCategories, gradeBisimplicial,
      gradeSSet]
    using (IsRealizationWeakEquivalence.of_isIso
      (TwoSidedBar.discreteNerveIso (d.RowGrade ⦋n⦌)).hom).comp hp

/-- Removing the constant nerve direction leaves the same actual grade simplicial set. -/
def gradeDiagonalIso : diagonalSSet d.gradeBisimplicial ≅ d.gradeSSet :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

/-- The grading map from the original Waldhausen simplicial set. -/
def gradeMap : sSet d.coarseStructure.cof d.coarseStructure.weq ⟶ d.gradeSSet :=
  (sSetWeakRowDiagonalIso d.coarseStructure).hom ≫ diagonalMap d.gradeNerveMap ≫
    d.gradeDiagonalIso.hom

/-- The literal original coarse grading map is a complete realization weak equivalence. -/
theorem gradeMap_isRealizationWeakEquivalence : IsRealizationWeakEquivalence d.gradeMap := by
  simpa only [IsRealizationWeakEquivalence, gradeMap, Functor.map_comp, TopCat.hom_comp,
    ContinuousMap.comp_assoc] using
    (IsRealizationWeakEquivalence.of_isIso d.gradeDiagonalIso.hom).comp
    ((BisimplicialRealization.diagonalMap_isRealizationWeakEquivalence d.gradeNerveMap
      d.gradeNerveMap_row_weak).comp
      (IsRealizationWeakEquivalence.of_isIso (sSetWeakRowDiagonalIso d.coarseStructure).hom))

/-- No object replacement occurs: every output coordinate is the grade of the original first row. -/
@[simp] theorem gradeMap_component (n : SimplexCategory)
    (X : (sSet d.coarseStructure.cof d.coarseStructure.weq).obj (op n)) (p : Interval n) :
    ((d.gradeMap.app (op n) X).val p) = d.value (X.val.obj (0, p)) := rfl

end CategoryTheory.Waldhausen.Cofinality.Grading
