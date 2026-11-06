/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremB.SkeletalCartesianStageExtraction
public import Colib.Topology.Category.TopCat.SequentialColimit.CompactCartesian

/-! Simultaneous characteristic-chart and finite replacement-stage induction. -/
/-! Implementation provenance: adapted from
`Quillen/CategoryTheory/TheoremB/SkeletalCartesianInduction.lean`
at c561118b7795eb9780be9ed391c3251d6a4d0afd, retaining the actual replacement charts,
base restrictions and canonical comparisons. The strict finite-stage coordinate transfer
`stageCartesian_of_restrictionCartesian` is extracted from the same revision of
`Quillen/CategoryTheory/TheoremB/SkeletalCartesianCoordinates.lean`. -/
@[expose] public section

open CategoryTheory.TheoremA SSet Topology.HomotopyPullback
open CategoryTheory.TheoremB


noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial Topology unitInterval
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.TheoremB.Skeletal
open TheoremA
variable {D : Type u} [SmallCategory D] (H : D ⥤ SSet.{u})

/-- Every simplex in the actual base skeleton has its canonical cartesian chart. -/
def StageCharts (n : ℕ) : Prop :=
  ∀ (k : ℕ) (s : (nerve D).obj (op ⦋k⦌))
    (hs : s ∈ ((nerve D).skeleton n).obj (op ⦋k⦌)),
      ChartCartesian H ((nerve D).skeleton n) s hs

/-- The initial skeleton is empty, so there are no characteristic obligations. -/
theorem stageCharts_zero : StageCharts H 0 := by
  intro k s hs
  simp only [(nerve D).skeleton_zero, Subfunctor.bot_obj] at hs
  exact False.elim hs

/-- The two outgoing conclusions of the attachment cube propagate all
charts: lower-dimensional ancestors use the old-stage square, and the new
nondegenerate cells use their characteristic squares. Simplicial
degeneracies are then handled by their exact enriched chart maps. -/
theorem StageCharts.succ {n : ℕ} (h : StageCharts H n)
    (hstep : RestrictionCartesian H ((nerve D).skeleton.monotone (Nat.le_succ n)))
    (hnew : ∀ s : (nerve D).nonDegenerate n,
      ChartCartesian H ((nerve D).skeleton (n + 1)) s.1 ((nerve D).mem_skeleton s.1)) :
    StageCharts H (n + 1) := by
  intro k s hs
  apply chartCartesian_of_nondegenerate H ((nerve D).skeleton (n + 1)) ?_ s hs
  intro j t ht
  have hj : j < n + 1 :=
    ((nerve D).mem_skeleton_obj_iff_of_nonDegenerate t (n + 1)).mp ht
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
  · have ht' : t.1 ∈ ((nerve D).skeleton n).obj (op ⦋j⦌) :=
      (nerve D).mem_skeleton t.1 hj
    exact ChartCartesian.enlarge H ((nerve D).skeleton.monotone (Nat.le_succ n))
      t.1 ht' (h j t.1 ht') hstep
  · exact hnew t

/-- Canonical successor restriction squares suffice to compare any two
finite stages. Pasting retains the prescribed constant-path comparison. -/
theorem restrictionCartesian_of_successors
    (hstep : ∀ n, RestrictionCartesian H ((nerve D).skeleton.monotone (Nat.le_succ n)))
    (k n : ℕ) (hkn : k ≤ n) :
    RestrictionCartesian H ((nerve D).skeleton.monotone hkn) := by
  induction n, hkn using Nat.le_induction with
  | base => exact RestrictionCartesian.refl H ((nerve D).skeleton k)
  | succ n hkn ih => exact RestrictionCartesian.trans H ih (hstep n)

/-- Changing the actual skeleton bases to the isomorphic point replacements
retains the canonical finite-stage comparison required by weak assembly. -/
theorem stageCartesian_of_restrictionCartesian (k n : ℕ) (h : k ≤ n)
    (hc : RestrictionCartesian H ((nerve D).skeleton.monotone h)) :
    ∃ e : ContinuousMap.HomotopyEquiv ((realizedReplacementSkeleton H).obj k)
      (Topology.HomotopyPullback.Sequential.StagePullback
        (replacementProjectionTowerMap H) k n h),
      e.toFun = Topology.HomotopyPullback.Sequential.stageComparison
        (replacementProjectionTowerMap H) k n h := by
  have hh : Cartesian ((replacementProjectionTowerMap H).app k).hom
      ((replacementProjectionTowerMap H).app n).hom
      ((realizedReplacementSkeleton H).map (homOfLE h)).hom
      ((realizedReplacementSkeleton pointDiagram).map (homOfLE h)).hom
      (congrArg TopCat.Hom.hom ((replacementProjectionTowerMap H).naturality (homOfLE h))) := by
    apply cartesianOfCoordinates _ _ _ _ _
      (SSet.toTop.map (restrictionProjection H ((nerve D).skeleton k))).hom
      (SSet.toTop.map (restrictionProjection H ((nerve D).skeleton n))).hom
      (SSet.toTop.map (diagonalMap
        (replacementRestrictionInclusion H ((nerve D).skeleton.monotone h)))).hom
      (SSet.toTop.map (SSet.Subcomplex.homOfLE ((nerve D).skeleton.monotone h))).hom
      (congrArg TopCat.Hom.hom
        (realizedRestriction_square H ((nerve D).skeleton.monotone h)))
      (Homeomorph.refl _) (Homeomorph.refl _)
      (pointRestrictionHomeomorph ((nerve D).skeleton k))
      (pointRestrictionHomeomorph ((nerve D).skeleton n))
    · exact congrArg TopCat.Hom.hom (pointRestrictionIso_projectionTower H k).symm
    · exact congrArg TopCat.Hom.hom (pointRestrictionIso_projectionTower H n).symm
    · rfl
    · exact congrArg TopCat.Hom.hom (pointRestrictionIso_baseTower h).symm
    · exact hc
  exact ⟨hh.equiv, hh.equiv_toFun⟩


variable
  (htrans : ∀ ⦃d e : D⦄ (f : d ⟶ e),
    ∃ E : ContinuousMap.HomotopyEquiv |H.obj d| |H.obj e|,
      E.toFun = (SSet.toTop.map (H.map f)).hom)

include htrans

/-- Under actual transition homotopy equivalences, every actual chart at
every finite stage is canonically homotopy cartesian. The induction starts
with the empty skeleton and derives both incoming faces at every step. -/
theorem stageCharts (n : ℕ) : StageCharts H n := by
  induction n with
  | zero => exact stageCharts_zero H
  | succ n ih =>
    obtain ⟨hstep, hnew⟩ := successor_restriction_and_chart H htrans n ih
    exact StageCharts.succ H ih hstep hnew

/-- Every actual successor restriction comparison is cartesian, with no
finite-stage or chart hypothesis supplied by the caller. -/
theorem stageRestrictionCartesian_succ (n : ℕ) :
    RestrictionCartesian H ((nerve D).skeleton.monotone (Nat.le_succ n)) :=
  (successor_restriction_and_chart H htrans n (stageCharts H htrans n)).1

/-- All finite base restrictions are canonically homotopy cartesian under
the transition hypothesis alone. -/
theorem stageRestrictionCartesian (k n : ℕ) (hkn : k ≤ n) :
    RestrictionCartesian H ((nerve D).skeleton.monotone hkn) :=
  restrictionCartesian_of_successors H (stageRestrictionCartesian_succ H htrans) k n hkn

/-- The complete finite-stage input to compact weak assembly, retaining
exactly its prescribed point-replacement tower comparison. -/
theorem stageComparison_cartesian (k n : ℕ) (hkn : k ≤ n) :
    ∃ e : ContinuousMap.HomotopyEquiv ((realizedReplacementSkeleton H).obj k)
      (Topology.HomotopyPullback.Sequential.StagePullback
        (replacementProjectionTowerMap H) k n hkn),
      e.toFun = Topology.HomotopyPullback.Sequential.stageComparison
        (replacementProjectionTowerMap H) k n hkn :=
  stageCartesian_of_restrictionCartesian H k n hkn
    (stageRestrictionCartesian H htrans k n hkn)

/-- A chosen equivalence for the actual finite-stage comparison. -/
def stageComparisonHomotopyEquiv (k n : ℕ) (hkn : k ≤ n) :
    ContinuousMap.HomotopyEquiv ((realizedReplacementSkeleton H).obj k)
      (Topology.HomotopyPullback.Sequential.StagePullback
        (replacementProjectionTowerMap H) k n hkn) :=
  (stageComparison_cartesian H htrans k n hkn).choose

@[simp]
theorem stageComparisonHomotopyEquiv_toFun (k n : ℕ) (hkn : k ≤ n) :
    (stageComparisonHomotopyEquiv H htrans k n hkn).toFun =
      Topology.HomotopyPullback.Sequential.stageComparison
        (replacementProjectionTowerMap H) k n hkn :=
  (stageComparison_cartesian H htrans k n hkn).choose_spec

end CategoryTheory.TheoremB.Skeletal
