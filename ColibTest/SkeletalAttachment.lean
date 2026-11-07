/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.Topology.Realization.Skeleton

/-! Regression: no Mono on single-step attachment. -/
@[expose] public noncomputable section
open CategoryTheory Limits Topology stdSimplex
open scoped Simplicial Topology
universe u
namespace SSet

example {A X : SSet.{u}} (i : A ⟶ X) (n : ℕ) :
    IsPushout (TopCat.parameterizedSimplexBoundaryInclusion (skeletalCellIndex i n) n)
      (realizedSkeletalAttaching i n) (realizedSkeletalCharacteristic i n)
      (SSet.toTop.map (SSet.relativeCellComplexOfMono.r i n)) := realizedSkeletal_isPushout i n

example {A X : SSet.{u}} (i : A ⟶ X) (n : ℕ) :
    IsClosedEmbedding (SSet.toTop.map (SSet.relativeCellComplexOfMono.r i n)) :=
  realizedSkeletal_transition_isClosedEmbedding i n

example {A X : SSet.{u}} (i : A ⟶ X) (n : ℕ) (hn : 2 ≤ n) :
    (FundamentalGroupoid.map
      (SSet.toTop.map (SSet.relativeCellComplexOfMono.r i n)).hom).Full :=
  realizedSkeletal_transition_fundamentalGroupoid_full i n hn

example {A X : SSet.{u}} (i : A ⟶ X) [Mono i] [T1Space |A|] (n : ℕ) :
    T1Space ((realizedRelativeSkeletonTower i).obj n) := inferInstance

example (X : SSet.{u}) (n : ℕ) :
    (realizedSkeletonStageIso X n).hom ≫ SSet.toTop.map (X.skeleton n).ι =
      (realizedSkeletonCocone X).ι.app n := realizedSkeletonStageIso_hom_ι X n

example (X : SSet.{u}) : T1Space |X| := inferInstance

example (X : SSet.{u}) (n : ℕ) :
    IsClosedEmbedding (SSet.toTop.map (X.skeleton n).ι) :=
  realization_skeleton_isClosedEmbedding X n

example {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] (X : SSet.{u}) (f : C(Y, |X|)) :
    ∃ n, ∃ g : C(Y, |(X.skeleton n : SSet.{u})|),
      ∀ y, SSet.toTop.map (X.skeleton n).ι (g y) = f y :=
  realization_continuousMap_factors_skeleton X f

example (X : SSet.{u}) (k : ℕ) (hk : 2 ≤ k)
    {x y : |(X.skeleton k : SSet.{u})|}
    (p : Path (SSet.toTop.map (X.skeleton k).ι x) (SSet.toTop.map (X.skeleton k).ι y)) :
    ∃ q : Path x y, (q.map (SSet.toTop.map (X.skeleton k).ι).hom.continuous).Homotopic p :=
  realization_skeleton_path_homotopic X k hk p

end SSet

#print axioms SSet.realizedSkeletal_isPushout
#print axioms SSet.realization_t1Space
#print axioms SSet.realization_skeleton_fundamentalGroupoid_full
#print axioms SSet.realization_skeleton_path_homotopic
