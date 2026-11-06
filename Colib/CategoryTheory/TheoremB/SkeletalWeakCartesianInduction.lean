/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.TheoremB.SkeletalWeakCartesianAssembly
public import Colib.CategoryTheory.TheoremB.SkeletalWeakCartesianDegeneracies
public import Colib.CategoryTheory.TheoremB.SequentialWeakCartesian

/-! # General weak-cartesian replacement skeleton induction

Implementation provenance:
`Quillen/CategoryTheory/TheoremB/SkeletalWeakCartesianInduction.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.TheoremA
open CategoryTheory.TheoremB


noncomputable section
open Topology TopCat SSet Topology.HomotopyPullback
open CategoryTheory Limits Opposite
open scoped Simplicial Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.TheoremB.Skeletal
open TheoremA
open CategoryTheory.TheoremB (replacementSkeletonComparison_isWeakHomotopyEquivalence_of_weakStages)
variable {D : Type u} [SmallCategory D] {H J : D ⥤ SSet.{u}} (η : H ⟶ J)

/-- All actual characteristic charts in one base skeleton are weak-cartesian. -/
def StageWeakCharts (n : ℕ) : Prop :=
  ∀ (k : ℕ) (s : (nerve D).obj (op ⦋k⦌))
    (hs : s ∈ ((nerve D).skeleton n).obj (op ⦋k⦌)),
      ChartWeakCartesian η ((nerve D).skeleton n) s hs

/-- The empty initial skeleton imposes no characteristic obligations. -/
theorem stageWeakCharts_zero : StageWeakCharts η 0 := by
  intro k s hs
  simp only [(nerve D).skeleton_zero, Subfunctor.bot_obj] at hs
  exact False.elim hs

/-- Propagation uses the original old-stage and new-cell comparisons;
degenerate charts descend through their actual inverse coefficient isomorphisms. -/
theorem StageWeakCharts.succ {n : ℕ} (h : StageWeakCharts η n)
    (hstep : RestrictionWeakCartesian η ((nerve D).skeleton.monotone (Nat.le_succ n)))
    (hnew : ∀ s : (nerve D).nonDegenerate n,
      ChartWeakCartesian η ((nerve D).skeleton (n + 1)) s.1 ((nerve D).mem_skeleton s.1)) :
    StageWeakCharts η (n + 1) := by
  intro k s hs
  apply chartWeakCartesian_of_nondegenerate η ((nerve D).skeleton (n + 1)) ?_ s hs
  intro j t ht
  have hj : j < n + 1 :=
    ((nerve D).mem_skeleton_obj_iff_of_nonDegenerate t (n + 1)).mp ht
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
  · have ht' : t.1 ∈ ((nerve D).skeleton n).obj (op ⦋j⦌) :=
      (nerve D).mem_skeleton t.1 hj
    exact ChartWeakCartesian.enlarge η ((nerve D).skeleton.monotone (Nat.le_succ n))
      t.1 ht' (h j t.1 ht') hstep
  · exact hnew t

/-- Original successor comparisons paste to every finite-stage comparison. -/
theorem restrictionWeakCartesian_of_successors
    (hstep : ∀ n, RestrictionWeakCartesian η ((nerve D).skeleton.monotone (Nat.le_succ n)))
    (k n : ℕ) (hkn : k ≤ n) :
    RestrictionWeakCartesian η ((nerve D).skeleton.monotone hkn) := by
  induction n, hkn using Nat.le_induction with
  | base => exact RestrictionWeakCartesian.refl η ((nerve D).skeleton k)
  | succ n hkn ih => exact RestrictionWeakCartesian.trans η ih (hstep n)

/-- All characteristic comparisons follow from weak original transition squares. -/
theorem stageWeakCharts (htrans : TransitionWeakCartesian η) (n : ℕ) : StageWeakCharts η n := by
  induction n with
  | zero => exact stageWeakCharts_zero η
  | succ n ih =>
    obtain ⟨hstep,hnew⟩ := successor_weakRestriction_and_chart η htrans n ih
    exact StageWeakCharts.succ η ih hstep hnew

/-- Every actual successor restriction has a weak canonical comparison. -/
theorem stageRestrictionWeakCartesian_succ (htrans : TransitionWeakCartesian η) (n : ℕ) :
    RestrictionWeakCartesian η ((nerve D).skeleton.monotone (Nat.le_succ n)) :=
  (successor_weakRestriction_and_chart η htrans n (stageWeakCharts η htrans n)).1

/-- Arbitrary finite-stage restrictions retain the original weak comparison. -/
theorem stageRestrictionWeakCartesian (htrans : TransitionWeakCartesian η)
    (k n : ℕ) (hkn : k ≤ n) :
    RestrictionWeakCartesian η ((nerve D).skeleton.monotone hkn) :=
  restrictionWeakCartesian_of_successors η (stageRestrictionWeakCartesian_succ η htrans) k n hkn

/-- Complete weakness of the literal finite-stage comparison for arbitrary η. -/
theorem stageComparison_isWeakHomotopyEquivalence (htrans : TransitionWeakCartesian η)
    (k n : ℕ) (hkn : k ≤ n) :
    IsWeakHomotopyEquivalence
      (Topology.HomotopyPullback.Sequential.stageComparison
        (realizedReplacementSkeletonMap η) k n hkn) :=
  stageWeakCartesian_of_restrictionWeakCartesian η k n hkn
    (stageRestrictionWeakCartesian η htrans k n hkn)

/-- Complete weakness of the original stage-to-realized-replacement comparison,
with every finite-stage premise discharged by the preceding induction. -/
theorem replacementSkeletonComparison_isWeakHomotopyEquivalence
    (htrans : TransitionWeakCartesian η) (k : ℕ) :
    IsWeakHomotopyEquivalence (CategoryTheory.TheoremB.replacementSkeletonComparison η k) :=
  replacementSkeletonComparison_isWeakHomotopyEquivalence_of_weakStages η k
    (fun n h ↦ stageComparison_isWeakHomotopyEquivalence η htrans k n h)

end CategoryTheory.TheoremB.Skeletal
