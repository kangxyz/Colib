/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.SourceEquivalence

/-! Strict source equivalences retain the actual homotopy-fiber path.

Implementation source: `Quillen/CategoryTheory/TheoremB/ReplacementVertex.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Only dependency ownership changes. -/
@[expose] public noncomputable section
open scoped Topology
universe u

namespace Topology.HomotopyFiber
variable {X Y B : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace B]

/-- Strictly commuting source equivalence, with no padding of the retained path. -/
def sourceEquivOfSquare (p : C(X, B)) (q : C(Y, B))
    (e : ContinuousMap.HomotopyEquiv X Y) (sq : q.comp e.toFun = p) (b : B) :
    ContinuousMap.HomotopyEquiv (HomotopyFiber p b) (HomotopyFiber q b) := by
  subst p
  exact sourceEquiv q e b

@[simp]
theorem sourceEquivOfSquare_toFun (p : C(X, B)) (q : C(Y, B))
    (e : ContinuousMap.HomotopyEquiv X Y) (sq : q.comp e.toFun = p) (b : B) :
    (sourceEquivOfSquare p q e sq b).toFun =
      map (f₁ := p) (f₂ := q) e.toFun (ContinuousMap.id B)
        (sq.symm : (ContinuousMap.id B).comp p = q.comp e.toFun) b := by
  subst p
  rfl

end Topology.HomotopyFiber
