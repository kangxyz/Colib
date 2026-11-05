/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.FiniteSkeleton
public import Colib.Topology.Category.TopCat.CompactHausdorffPushout

/-! # Genuine Hausdorffness and local compactness of finite realizations

Each actual skeletal stage is obtained by a finite compact-Hausdorff cell
attachment. Compactness then factors the identity of the finite realization
through one such stage. The resulting continuous injection transfers the
Hausdorff separation property to the unchanged actual realization.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory TopCat
open scoped Simplicial Topology
universe u

namespace SSet

/-- Every actual skeletal stage of a finite simplicial set is Hausdorff. -/
instance realizationFinite_skeletonStage_t2Space (X : SSet.{u}) [X.Finite] (n : ℕ) :
    T2Space ((realizedSkeletonTower X).obj n) := by
  induction n with
  | zero => exact realizationSkeleton_zero_t2Space X
  | succ n ih =>
    let : Finite (skeletalCellIndex ((⊥ : X.Subcomplex).ι) n) :=
      inferInstanceAs (Finite (SSet.relativeCellComplexOfMono.Cell ((⊥ : X.Subcomplex).ι) n))
    let : T2Space |(SSet.skeletonOfMono ((⊥ : X.Subcomplex).ι) n : SSet.{u})| := ih
    exact t2Space_pushout_of_compact_closedEmbedding
      (realizedSkeletal_isPushout ((⊥ : X.Subcomplex).ι) n)
      (isClosedEmbedding_parameterizedSimplexBoundary (skeletalCellIndex ((⊥ : X.Subcomplex).ι)
        n) n)

/-- The actual realization of every finite simplicial set is Hausdorff. -/
instance realizationFinite_t2Space (X : SSet.{u}) [X.Finite] : T2Space |X| := by
  obtain ⟨n, g, hg⟩ := realizationFinite_injective_skeletonFactor X
  exact T2Space.of_injective_continuous hg g.continuous

/-- Compact Hausdorff finite realizations have genuine local compactness. -/
instance realizationFinite_locallyCompactSpace (X : SSet.{u}) [X.Finite] :
    LocallyCompactSpace |X| := inferInstance

end SSet
