/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Covering.HomotopyPullbackTransfer
public import Mathlib.Topology.FiberBundle.Constructions

/-!
# Literal bundle pullbacks and strict subspace pullbacks

The bundle pullback keeps Mathlib's actual induced
pullback topology. Its homeomorphism to the ordinary subtype pullback is
proved from the pinned inducing theorem, rather than installing a replacement
topology. Discrete fiber bundles therefore give actual covers after base change.
-/

/-! Implementation source: `Quillen/Topology/Covering/FiberBundlePullback.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual topologies,
path classes, dependent endpoint equalities and covering maps are retained. -/
@[expose] public section

open Topology
noncomputable section
open Bundle
open scoped Topology
universe u
namespace Topology.Covering

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  (F : Type u) (E : Y → Type u) [TopologicalSpace (TotalSpace F E)]

/-- The underlying bundle pullback is the exact strict matching-pair subtype. -/
def pullbackStrictEquiv (f : C(X, Y)) :
    TotalSpace F ((f : X → Y) *ᵖ E) ≃
      {z : X × TotalSpace F E // z.2.proj = f z.1} where
  toFun z := ⟨(z.proj, Pullback.lift f z), rfl⟩
  invFun z := ⟨z.1.1, show E (f z.1.1) from z.2 ▸ z.1.2.snd⟩
  left_inv z := by cases z; rfl
  right_inv z := by
    rcases z with ⟨⟨x, ⟨y, v⟩⟩, h⟩
    dsimp at h
    cases h
    rfl

/-- The exact pullback topology agrees homeomorphically with the strict subtype topology. -/
def pullbackStrictHomeomorph (f : C(X, Y)) :
    TotalSpace F ((f : X → Y) *ᵖ E) ≃ₜ
      {z : X × TotalSpace F E // z.2.proj = f z.1} :=
  (pullbackStrictEquiv F E f).toHomeomorphOfIsInducing
    (IsInducing.subtypeVal.of_comp_iff.mp (inducing_pullbackTotalSpaceEmbedding F E f))

/-- Both actual coordinates are retained by the topology comparison. -/
theorem pullbackStrictHomeomorph_apply (f : C(X, Y))
    (z : TotalSpace F ((f : X → Y) *ᵖ E)) :
    (pullbackStrictHomeomorph F E f z).val = (z.proj, Pullback.lift f z) := rfl

omit [TopologicalSpace (TotalSpace F E)] in
/-- Surjectivity is proved separately from the covering predicate. -/
theorem pullback_projection_surjective [∀ y, Nonempty (E y)] (f : C(X, Y)) :
    Function.Surjective (π F ((f : X → Y) *ᵖ E)) := by
  intro x
  exact ⟨⟨x, Classical.choice (inferInstance : Nonempty (E (f x)))⟩, rfl⟩

variable [TopologicalSpace F] [DiscreteTopology F] [∀ y, TopologicalSpace (E y)]
  [FiberBundle F E]

/-- Mathlib's literal pullback of the discrete fiber bundle is an actual covering. -/
theorem isCoveringMap_pullback_projection [∀ y, Nonempty (E y)] (f : C(X, Y)) :
    IsCoveringMap (π F ((f : X → Y) *ᵖ E)) := by
  let := FiberBundle.pullback (F := F) (E := E) f
  exact FiberBundle.isCoveringMap

/-- The literal bundle pullback along a genuine HE is genuinely equivalent to the old total. -/
def pullbackTotalHomotopyEquiv (e : ContinuousMap.HomotopyEquiv X Y) :
    ContinuousMap.HomotopyEquiv (TotalSpace F ((e.toFun : X → Y) *ᵖ E)) (TotalSpace F E) :=
  (pullbackStrictHomeomorph F E e.toFun).toHomotopyEquiv.trans
    (strictPullbackSourceHomotopyEquiv ⟨π F E, FiberBundle.isCoveringMap.continuous⟩
      FiberBundle.isCoveringMap e)

/-- The actual total equivalence has the original bundle pullback lift as forward map. -/
theorem pullbackTotalHomotopyEquiv_apply (e : ContinuousMap.HomotopyEquiv X Y)
    (z : TotalSpace F ((e.toFun : X → Y) *ᵖ E)) :
    pullbackTotalHomotopyEquiv F E e z = Pullback.lift e.toFun z := rfl

/-- A simply connected discrete-bundle total stays simply connected under genuine HE base change. -/
theorem pullback_simplyConnectedSpace (e : ContinuousMap.HomotopyEquiv X Y)
    [SimplyConnectedSpace (TotalSpace F E)] :
    SimplyConnectedSpace (TotalSpace F ((e.toFun : X → Y) *ᵖ E)) :=
  (pullbackTotalHomotopyEquiv F E e).simplyConnectedSpace

end Topology.Covering
