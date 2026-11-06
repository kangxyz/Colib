/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Colib.CategoryTheory.TheoremA.ReplacementInvariance
public import Colib.Topology.Realization.MonomorphismEmbedding
public import Colib.Topology.Category.TopCat.SequentialColimit.CompactCartesian

/-!
# Compact cartesian assembly for actual replacement skeleta

The base-restricted replacement tower has T₁ stages and closed-embedding
successor maps. Consequently the sequential cartesian theorem applies to
its actual diagonal realization. The geometric finite-stage cartesian
comparisons remain explicit inputs; a stagewise equivalence of total spaces
is neither assumed nor substituted for them.
-/
/-! Implementation provenance: adapted from
`Quillen/CategoryTheory/TheoremB/ReplacementSkeletonCompact.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual replacement tower,
closed embeddings, cocone and all-degree comparison maps are retained. -/
@[expose] public section

open Topology SSet

open CategoryTheory.TheoremA


noncomputable section
open CategoryTheory Limits
open scoped Simplicial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.TheoremA

variable {D : Type u} [SmallCategory D] (H : D ⥤ SSet.{u})

/-- Every realized stage of a base-restricted replacement is T₁. -/
instance realizedReplacementSkeleton_t1Space (n : ℕ) :
    T1Space ((realizedReplacementSkeleton H).obj n) :=
  inferInstanceAs (T1Space |diagonalSSet ((replacementSkeleton H).obj n)|)

/-- Every transition of the actual realized base-skeleton tower is a
closed embedding, not merely a cofibration. -/
theorem realizedReplacementSkeleton_isClosedEmbedding {n m : ℕ} (f : n ⟶ m) :
    IsClosedEmbedding ((realizedReplacementSkeleton H).map f) := by
  let i := diagonalFunctor.map ((replacementSkeleton H).map f)
  have : Mono i := by
    apply (NatTrans.mono_iff_mono_app i).mpr
    intro p
    change Mono ((((replacementSkeleton H).map f).app p).app p)
    infer_instance
  exact realization_mono_isClosedEmbedding i

/-- Closed-embedding hypotheses for the canonical sequential assembly. -/
theorem realizedReplacementSkeleton_closedEmbeddings (n : ℕ) :
    IsClosedEmbedding ((realizedReplacementSkeleton H).map (homOfLE (Nat.le_succ n))) :=
  realizedReplacementSkeleton_isClosedEmbedding H _

end CategoryTheory.TheoremA

namespace CategoryTheory.TheoremB
open TheoremA Topology.HomotopyPullback.Sequential

variable {D : Type u} [SmallCategory D] {H K : D ⥤ SSet.{u}} (η : H ⟶ K)

/-- Finite-stage pullbacks for the actual diagonal-realized replacement
map. These are the geometric comparisons needed by cartesian gluing. -/
abbrev ReplacementStagePullback (k n : ℕ) (h : k ≤ n) :=
  StagePullback (realizedReplacementSkeletonMap η) k n h

/-- The actual stage-to-total-realization homotopy pullback. -/
abbrev ReplacementColimitPullback (k : ℕ) :=
  ColimitPullback (realizedReplacementSkeletonMap η)
    (realizedReplacementSkeletonCocone H) (realizedReplacementSkeletonIsColimit H)
    (realizedReplacementSkeletonCocone K) k

/-- The specified canonical stage-to-total comparison. Its source is the
actual realized base restriction, not a finite-cell approximation. -/
abbrev replacementSkeletonComparison (k : ℕ) :=
  colimitComparison (realizedReplacementSkeletonMap η)
    (realizedReplacementSkeletonCocone H) (realizedReplacementSkeletonIsColimit H)
    (realizedReplacementSkeletonCocone K) k

/-- The only remaining input for weak cartesian assembly of the actual
simplicial replacement is finite-stage homotopy cartesianness. Separation,
closed embeddings, the actual colimit, and compact relative homotopy
factorization have all been proved. -/
theorem replacementSkeletonComparison_bijective (k : ℕ)
    (e : ∀ n (h : k ≤ n), ContinuousMap.HomotopyEquiv
      ((realizedReplacementSkeleton H).obj k) (ReplacementStagePullback η k n h))
    (he : ∀ n h, (e n h).toFun = stageComparison (realizedReplacementSkeletonMap η) k n h)
    (x : (realizedReplacementSkeleton H).obj k) (q : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin q)
      (replacementSkeletonComparison η k) (x := x) rfl) :=
  colimitComparison_homotopyGroupMap_bijective (realizedReplacementSkeletonMap η)
    (realizedReplacementSkeletonCocone H) (realizedReplacementSkeletonIsColimit H)
    (realizedReplacementSkeletonCocone K) (realizedReplacementSkeletonIsColimit K)
    (realizedReplacementSkeleton_closedEmbeddings H)
    (realizedReplacementSkeleton_closedEmbeddings K) k e he x q

/-- Every component of the actual replacement stage-to-colimit pullback is
reached by the canonical comparison, without assuming a nonempty stage. -/
theorem replacementSkeletonComparison_component_surjective (k : ℕ)
    (e : ∀ n (h : k ≤ n), ContinuousMap.HomotopyEquiv
      ((realizedReplacementSkeleton H).obj k) (ReplacementStagePullback η k n h))
    (he : ∀ n h, (e n h).toFun = stageComparison (realizedReplacementSkeletonMap η) k n h)
    (y : ReplacementColimitPullback η k) :
    ∃ x : (realizedReplacementSkeleton H).obj k, Joined (replacementSkeletonComparison η k x) y :=
  colimitComparison_component_surjective (realizedReplacementSkeletonMap η)
    (realizedReplacementSkeletonCocone H) (realizedReplacementSkeletonIsColimit H)
    (realizedReplacementSkeletonCocone K) (realizedReplacementSkeletonIsColimit K)
    (realizedReplacementSkeleton_closedEmbeddings H)
    (realizedReplacementSkeleton_closedEmbeddings K) k e he y

end CategoryTheory.TheoremB
