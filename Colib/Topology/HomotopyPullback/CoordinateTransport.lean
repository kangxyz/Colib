/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyPullback.Cartesian

/-! Forward transport of the canonical cartesian comparison through
strictly compatible homeomorphic coordinates. -/
/-! Implementation source: `Quillen/Topology/Realization/Cartesian/CoordinateTransport.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual coproduct topologies and canonical
constant-path comparisons are retained. -/
@[expose] public section

noncomputable section
universe u
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace Topology.HomotopyPullback

/-- The forward direction of cartesian coordinate transport. The same
four strictly compatible homeomorphisms preserve the actual canonical
comparison in either direction. -/
theorem cartesianToCoordinates {W X A B W' X' A' B' : Type u}
    [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace W'] [TopologicalSpace X'] [TopologicalSpace A'] [TopologicalSpace B']
    (p : C(W, A)) (q : C(X, B)) (f : C(W, X)) (g : C(A, B))
    (w : q.comp f = g.comp p)
    (p' : C(W', A')) (q' : C(X', B')) (f' : C(W', X')) (g' : C(A', B'))
    (w' : q'.comp f' = g'.comp p')
    (eW : W ≃ₜ W') (eX : X ≃ₜ X') (eA : A ≃ₜ A') (eB : B ≃ₜ B')
    (wp : p'.comp (eW : C(W, W')) = (eA : C(A, A')).comp p)
    (wq : q'.comp (eX : C(X, X')) = (eB : C(B, B')).comp q)
    (wf : f'.comp (eW : C(W, W')) = (eX : C(X, X')).comp f)
    (wg : g'.comp (eA : C(A, A')) = (eB : C(B, B')).comp g)
    (h : Cartesian p q f g w) : Cartesian p' q' f' g' w' := by
  apply cartesianOfCoordinates p' q' f' g' w' p q f g w
    eW.symm eX.symm eA.symm eB.symm
  · ext x
    apply eA.injective
    simpa using (ContinuousMap.congr_fun wp (eW.symm x)).symm
  · ext x
    apply eB.injective
    simpa using (ContinuousMap.congr_fun wq (eX.symm x)).symm
  · ext x
    apply eX.injective
    simpa using (ContinuousMap.congr_fun wf (eW.symm x)).symm
  · ext x
    apply eB.injective
    simpa using (ContinuousMap.congr_fun wg (eA.symm x)).symm
  · exact h

end Topology.HomotopyPullback
