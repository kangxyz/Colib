/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.DiscreteWeakComparison
public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalenceProperty

/-! Complete weak equivalences restrict to strict fibers over a discrete base.

Implementation source: the discrete-fiber theorem in
`Quillen/CategoryTheory/TheoremB/WeakVertexComparison.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. No weak-transition induction is imported. -/
@[expose] public noncomputable section
open scoped Topology unitInterval
universe u v w
namespace Topology

/-- Complete weakness restricts to strict fibers over a discrete base,
including component surjectivity when the chosen source fiber might be empty. -/
theorem discreteStrictFiberMap_isWeakHomotopyEquivalence
    {X : Type u} {Y : Type v} {B : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace B] [DiscreteTopology B]
    (p : C(X, B)) (q : C(Y, B)) (f : C(X, Y)) (sq : q.comp f = p) (b : B)
    (hf : IsWeakHomotopyEquivalence f) :
    IsWeakHomotopyEquivalence (discreteStrictFiberMap p q f sq b) where
  component_surjective y := by
    obtain ⟨x, hx⟩ := hf.component_surjective y.val
    let γ := hx.somePath
    have hconst (s t : unitInterval) : q (γ s) = q (γ t) :=
      TotallyDisconnectedSpace.eq_of_continuous (fun r => q (γ r)) (by fun_prop) s t
    have hb (t : unitInterval) : q (γ t) = b :=
      (hconst t 1).trans ((congrArg q γ.target).trans y.property)
    have hp : p x = b := (ContinuousMap.congr_fun sq x).symm.trans
      ((congrArg q γ.source).symm.trans (hb 0))
    refine ⟨⟨x, hp⟩, ⟨?_⟩⟩
    exact {
      toFun := fun t => ⟨γ t, hb t⟩
      continuous_toFun := by fun_prop
      source' := Subtype.ext γ.source
      target' := Subtype.ext γ.target }
  homotopy_bijective x n :=
    homotopyGroupMap_bijective_discreteStrictFiber p q f sq b x
      (hf.homotopy_bijective x.val n)

end Topology
