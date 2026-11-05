/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.FiniteCompact

/-! # Finite cell indices and genuine finite-stage retraction

Finite realizations are compact, so their identity maps factor through one
actual skeletal stage. This provides a continuous injection into that stage,
allowing its separation properties to be transferred without choosing a
numeric dimension bound or changing the realization model.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Simplicial Topology
universe u

namespace SSet

/-- Every degree of a finite simplicial set has finitely many actual cells. -/
instance finite_relativeSkeletalCells {A X : SSet.{u}} (i : A ⟶ X) [X.Finite] (n : ℕ) :
    Finite (SSet.relativeCellComplexOfMono.Cell i n) :=
  Finite.of_injective (fun c ↦ c.simplex) (by
    intro a b h
    cases a
    cases b
    cases h
    rfl)

/-- Every actual skeletal stage of a finite simplicial set is compact. -/
instance realizationFinite_skeletonStage_compactSpace (X : SSet.{u}) [X.Finite] (n : ℕ) :
    CompactSpace ((realizedSkeletonTower X).obj n) := by
  change CompactSpace |(SSet.skeletonOfMono ((⊥ : X.Subcomplex).ι) n : SSet.{u})|
  infer_instance

/-- The original zero stage is Hausdorff because it is genuinely empty. -/
instance realizationSkeleton_zero_t2Space (X : SSet.{u}) :
    T2Space ((realizedSkeletonTower X).obj 0) :=
  (TopCat.homeoOfIso (SSet.toTop.mapIso
    (SSet.relativeCellComplexOfMono ((⊥ : X.Subcomplex).ι)).isoBot)).symm.t2Space

/-- Compactness factors the actual identity map through one genuine skeletal
stage. Its continuous factor is therefore injective. -/
theorem realizationFinite_injective_skeletonFactor (X : SSet.{u}) [X.Finite] :
    ∃ n : ℕ, ∃ g : C(|X|, (realizedSkeletonTower X).obj n), Function.Injective g := by
  obtain ⟨n, g, hg⟩ := realization_continuousMap_factors X (ContinuousMap.id |X|)
  refine ⟨n, g, fun x y h ↦ ?_⟩
  exact (hg x).symm.trans ((congrArg ((realizedSkeletonCocone X).ι.app n) h).trans (hg y))

end SSet
