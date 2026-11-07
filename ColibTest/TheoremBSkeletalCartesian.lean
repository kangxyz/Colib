/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

import Colib.CategoryTheory.TheoremB.SkeletalCartesianInduction

/-! The ordinary finite-stage theorem uses only actual transition homotopy equivalences. -/

open CategoryTheory CategoryTheory.TheoremA CategoryTheory.TheoremB
open Topology.HomotopyPullback
open scoped Simplicial Topology

universe u

noncomputable section

variable {D : Type u} [SmallCategory D] (H : D ⥤ SSet.{u})
  (htrans : ∀ ⦃d e : D⦄ (f : d ⟶ e),
    ∃ E : ContinuousMap.HomotopyEquiv |H.obj d| |H.obj e|,
      E.toFun = (SSet.toTop.map (H.map f)).hom)

example (n : ℕ) : Skeletal.StageCharts H n := Skeletal.stageCharts H htrans n

example (k n : ℕ) (hkn : k ≤ n) :
    Skeletal.RestrictionCartesian H ((nerve D).skeleton.monotone hkn) :=
  Skeletal.stageRestrictionCartesian H htrans k n hkn

example (k n : ℕ) (hkn : k ≤ n) :
    ContinuousMap.HomotopyEquiv ((realizedReplacementSkeleton H).obj k)
      (Sequential.StagePullback (replacementProjectionTowerMap H) k n hkn) :=
  Skeletal.stageComparisonHomotopyEquiv H htrans k n hkn

example (k n : ℕ) (hkn : k ≤ n) :
    (Skeletal.stageComparisonHomotopyEquiv H htrans k n hkn).toFun =
      Sequential.stageComparison (replacementProjectionTowerMap H) k n hkn :=
  Skeletal.stageComparisonHomotopyEquiv_toFun H htrans k n hkn
