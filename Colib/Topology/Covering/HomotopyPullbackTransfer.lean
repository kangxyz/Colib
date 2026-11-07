/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyPullback.Fibration
public import Colib.Topology.HomotopyPullback.Symmetry
public import Mathlib.Topology.Homotopy.Lifting

/-!
# Actual total-space equivalence for covering pullbacks

Covering homotopy lifting compares the literal strict
pullback with the actual path-space pullback. A genuine parameter homotopy
equivalence then gives a genuine equivalence to the old covering total space.
The composite forward map is exactly the old-total projection. No local
connectedness or semilocal property is transferred by homotopy invariance.
-/

/-! Implementation source: `Quillen/Topology/Covering/HomotopyPullbackTransfer.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual topologies,
path classes, dependent endpoint equalities and covering maps are retained. -/
@[expose] public section
noncomputable section
open scoped Topology unitInterval
universe u
namespace Topology.Covering

variable {T X Y : Type u} [TopologicalSpace T] [TopologicalSpace X] [TopologicalSpace Y]

/-- Pinned covering lifts supply the full parameter-space homotopy lifting property. -/
theorem homotopyLiftingProperty (p : C(T, Y)) (hp : IsCoveringMap p) :
    Topology.HomotopyLiftingProperty p := by
  intro A _ a H hzero
  refine ⟨hp.liftHomotopy H a hzero, hp.liftHomotopy_zero H a hzero, ?_⟩
  intro t x
  exact congr_fun (hp.liftHomotopy_lifts H a hzero) (t, x)

/-- The literal strict pullback total space is genuinely equivalent to the old total space. -/
def strictPullbackSourceHomotopyEquiv (p : C(T, Y)) (hp : IsCoveringMap p)
    (e : ContinuousMap.HomotopyEquiv X Y) :
    ContinuousMap.HomotopyEquiv {z : X × T // p z.2 = e z.1} T :=
  (HomotopyPullback.strictPullbackHomotopyEquivOfLifting p e.toFun
    (homotopyLiftingProperty p hp)).trans
      (HomotopyPullback.sourceProjectionEquivOfParameterEquiv p e.toFun e rfl)

/-- The forward total-space comparison retains exactly the original covering point. -/
theorem strictPullbackSourceHomotopyEquiv_apply (p : C(T, Y)) (hp : IsCoveringMap p)
    (e : ContinuousMap.HomotopyEquiv X Y) (z : {z : X × T // p z.2 = e z.1}) :
    strictPullbackSourceHomotopyEquiv p hp e z = z.1.2 := rfl

/-- Simple connectedness transfers through the actual total-space equivalence. -/
theorem strictPullback_simplyConnectedSpace (p : C(T, Y)) (hp : IsCoveringMap p)
    (e : ContinuousMap.HomotopyEquiv X Y) [SimplyConnectedSpace T] :
    SimplyConnectedSpace {z : X × T // p z.2 = e z.1} :=
  (strictPullbackSourceHomotopyEquiv p hp e).simplyConnectedSpace

/-- Ordinary path connectedness, unlike local path connectedness, transports along a genuine HE. -/
theorem pathConnectedSpace_target [PathConnectedSpace X]
    (e : ContinuousMap.HomotopyEquiv X Y) : PathConnectedSpace Y where
  nonempty := Nonempty.map e PathConnectedSpace.nonempty
  joined y z := ⟨(e.right_inv.some.evalAt y).symm.trans
    (((PathConnectedSpace.somePath (e.invFun y) (e.invFun z)).map e.continuous).trans
      (e.right_inv.some.evalAt z))⟩

end Topology.Covering
