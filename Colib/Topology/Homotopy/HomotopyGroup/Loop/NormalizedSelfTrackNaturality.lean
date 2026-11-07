/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.GenLoopNormalizedSelfTrack

/-!
# Pointwise dependence of the actual normalized self-track

All reparametrizations in inverse-prefix normalization are independent of the
ambient space and of residual cube coordinates. This pointwise fact retains
both cancellations and the actual middle self-track. It is a point-set lemma,
not spatial additivity or stable compatibility.
-/
/-! Implementation source:
`Quillen/Topology/HomotopyGroups/Loop/NormalizedSelfTrackNaturality.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, basepoints,
coordinate order and signs are retained under native Colib ownership. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
universe u v w
namespace Topology

/-- Pointwise agreement of the original loop and self-track persists through normalization. -/
theorem loopNormalizedSelfTrack_pointwise {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
    (a : X → Z) (b : Y → Z) (γ : Path x x) (δ : Path y y)
    (α : Path γ γ) (β : Path δ δ)
    (hγ : ∀ s, a (γ s) = b (δ s))
    (hα : ∀ t s, a (α t s) = b (β t s)) (t s : unitInterval) :
    a (loopNormalizedSelfTrack γ α t s) = b (loopNormalizedSelfTrack δ β t s) := by
  have hc (r s : unitInterval) :
      a (loopInversePrefixCancellation γ r s) = b (loopInversePrefixCancellation δ r s) :=
    hγ _
  have hm (r s : unitInterval) :
      a ((loopLeftTranslationEquiv γ.symm (α r)) s) =
        b ((loopLeftTranslationEquiv δ.symm (β r)) s) := by
    rw [loopLeftTranslationEquiv_apply, loopLeftTranslationEquiv_apply,
      Path.trans_apply, Path.trans_apply]
    split_ifs
    · exact hγ _
    · exact hα _ _
  simp only [loopNormalizedSelfTrack, Path.trans_apply, Path.cast_coe, Path.map_coe,
    Function.comp_apply]
  split_ifs <;> first | exact hc _ _ | exact hm _ _

/-- Based postcomposition preserves the complete normalized path and its two cancellations. -/
theorem loopNormalizedSelfTrack_naturality {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
    (f : C(X, Y)) (h : f x = y) (γ : Path x x) (α : Path γ γ) :
    basedLoopMap (basedLoopMap f h) (basedLoopMap_refl f h)
        (loopNormalizedSelfTrack γ α) =
      loopNormalizedSelfTrack (basedLoopMap f h γ)
        (α.map (basedLoopMap f h).continuous) := by
  ext t s
  exact loopNormalizedSelfTrack_pointwise f id γ (basedLoopMap f h γ) α
    (α.map (basedLoopMap f h).continuous) (fun _ ↦ rfl) (fun _ _ ↦ rfl) t s

end Topology
