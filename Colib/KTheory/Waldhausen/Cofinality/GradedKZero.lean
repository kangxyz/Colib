/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Cofinality.GradedGroupRealization
public import Colib.Topology.ClassifyingSpace.FundamentalGroup

/-! # The actual original coarse K-zero group and the realized grade group

The original group-grading map preserves the actual zero vertex. Its genuine
weak equivalence on realization and the original realized-arrow fundamental
group calculation identify the literal coarse K-zero endpoint with the exact
actual object-grade range.

Implementation provenance: `Quillen/Waldhausen/Cofinality/GradedKZero.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
objects, maps and hypotheses are retained.
-/
@[expose] public section

noncomputable section
open Topology SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u
namespace CategoryTheory.Waldhausen.Cofinality.Grading
variable {C G : Type u} [SmallCategory C] [AddCommGroup G]
  {W : Structure C} (d : Grading W G) (T : FunctorialFactorization W)

/-- The original group-grading simplex sends the actual zero vertex to the actual group vertex. -/
theorem groupGradeMap_zero_vertex :
    (d.groupGradeMap T).app (op ⦋0⦌)
      (zeroSimplex d.coarseStructure.cof d.coarseStructure.weq W.zero W.isZero (op ⦋0⦌)) =
      nerveVertex (SingleObj.star (Multiplicative (d.valueRange T))) := by
  obtain ⟨x, hx⟩ := ComposableArrows.mk₀_surjective
    ((d.groupGradeMap T).app (op ⦋0⦌)
      (zeroSimplex d.coarseStructure.cof d.coarseStructure.weq W.zero W.isZero (op ⦋0⦌)))
  exact hx.trans (congrArg ComposableArrows.mk₀ (Subsingleton.elim x _))

/-- The unchanged continuous group-grading map preserves the original chosen basepoint. -/
theorem groupGradeMap_basepoint :
    (SSet.toTop.map (d.groupGradeMap T)).hom d.coarseStructure.kBasepoint =
      classifyingSpacePoint (SingleObj.star (Multiplicative (d.valueRange T))) := by
  change (SSet.toTop.map (d.groupGradeMap T))
    (realizationPoint (zeroSimplex d.coarseStructure.cof d.coarseStructure.weq W.zero W.isZero
      (op ⦋0⦌))) = _
  rw [realizationPoint_naturality, d.groupGradeMap_zero_vertex T]
  rfl

/-- The actual original grade map, based at the actual original zero object. -/
def coarseKZeroToGroupPi : d.coarseStructure.K 0 →*
    HomotopyGroup.Pi 1 (ClassifyingSpace (SingleObj (Multiplicative (d.valueRange T))))
      (classifyingSpacePoint (SingleObj.star (Multiplicative (d.valueRange T)))) :=
  HomotopyGroup.mapHom (SSet.toTop.map (d.groupGradeMap T)).hom (d.groupGradeMap_basepoint T)

/-- Complete weakness gives bijectivity of this same based original homomorphism. -/
theorem coarseKZeroToGroupPi_bijective : Function.Bijective (d.coarseKZeroToGroupPi T) := by
  have hh (y : ClassifyingSpace (SingleObj (Multiplicative (d.valueRange T))))
      (hy : (SSet.toTop.map (d.groupGradeMap T)).hom d.coarseStructure.kBasepoint = y) :
      Function.Bijective (HomotopyGroup.map (N := Fin 1)
        (SSet.toTop.map (d.groupGradeMap T)).hom hy) := by
    subst y
    exact (d.groupGradeMap_isRealizationWeakEquivalence T).homotopy_bijective
      d.coarseStructure.kBasepoint 1
  exact hh _ (d.groupGradeMap_basepoint T)

/-- The literal original coarse K-zero group is the exact actual object-value group. -/
def coarseKZeroEquiv : d.coarseStructure.K 0 ≃* Multiplicative (d.valueRange T) :=
  (MulEquiv.ofBijective (d.coarseKZeroToGroupPi T) (d.coarseKZeroToGroupPi_bijective T)).trans
    (GroupoidClassifying.singleObjPiOneEquiv (Multiplicative (d.valueRange T))).symm

end CategoryTheory.Waldhausen.Cofinality.Grading
