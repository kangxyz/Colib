/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Covering.FiberBundlePullback
public import Colib.Topology.Covering.PathClassSimplyConnected

/-!
# Constructed covers on spaces genuinely equivalent to locally equiconnected spaces

The frozen path-class universality construction supplies the original cover.
Only ordinary path connectedness is transported.
The source space retains its exact topology and is covered by the literal
pullback of the constructed discrete path-class bundle.
-/

/-! Implementation source: `Quillen/Topology/Covering/LocalConnectorTransfer.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual topologies,
path classes, dependent endpoint equalities and covering maps are retained. -/
@[expose] public section
noncomputable section
open Bundle
open scoped Topology
universe u
namespace Topology.Covering

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- The literal path-class pullback supplies all three actual cover properties. -/
theorem pathClass_pullback_properties [PathConnectedSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (E : LocalEquiconnection Y) (b : Y) :
    letI := E.locallyPathConnectedSpace
    let A := E.pathThinNeighborhoods
    letI := (A.prebundle b).totalSpaceTopology
    IsCoveringMap (π (PathClassFiber b b) ((e.toFun : X → Y) *ᵖ (PathClassFiber b))) ∧
      Function.Surjective (π (PathClassFiber b b) ((e.toFun : X → Y) *ᵖ (PathClassFiber b))) ∧
      SimplyConnectedSpace
        (TotalSpace (PathClassFiber b b) ((e.toFun : X → Y) *ᵖ (PathClassFiber b))) := by
  let := E.locallyPathConnectedSpace
  let A := E.pathThinNeighborhoods
  let := (A.prebundle b).totalSpaceTopology
  let := (A.prebundle b).toFiberBundle
  let : ∀ y, Nonempty (PathClassFiber b y) := fun y =>
    ⟨PathClassFiber.ofQuotient (.mk (PathConnectedSpace.somePath b y))⟩
  let := A.total_simplyConnectedSpace b
  exact ⟨isCoveringMap_pullback_projection (PathClassFiber b b) (PathClassFiber b) e.toFun,
    pullback_projection_surjective (PathClassFiber b b) (PathClassFiber b) e.toFun,
    pullback_simplyConnectedSpace (PathClassFiber b b) (PathClassFiber b) e⟩

/-- A genuine HE to a local-connector space constructs a simply connected surjective cover
on the original pathconnected source, with no local regularity hypothesis on that source. -/
theorem exists_simplyConnected_cover_of_localEquiconnection [PathConnectedSpace X]
    (e : ContinuousMap.HomotopyEquiv X Y) (E : LocalEquiconnection Y) (x : X) :
    ∃ T : Type u, ∃ t : TopologicalSpace T,
      let := t
      ∃ p : C(T, X), IsCoveringMap p ∧ Function.Surjective p ∧ SimplyConnectedSpace T := by
  let := pathConnectedSpace_target e
  let := E.locallyPathConnectedSpace
  let A := E.pathThinNeighborhoods
  let b := e x
  let := (A.prebundle b).totalSpaceTopology
  let T := TotalSpace (PathClassFiber b b) ((e.toFun : X → Y) *ᵖ (PathClassFiber b))
  let p : C(T, X) :=
    ⟨π (PathClassFiber b b) ((e.toFun : X → Y) *ᵖ (PathClassFiber b)),
      Pullback.continuous_proj (PathClassFiber b b) (PathClassFiber b) e.toFun⟩
  exact ⟨T, inferInstance, p, pathClass_pullback_properties e E b⟩

end Topology.Covering
