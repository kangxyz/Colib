/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.WeakCriterion
public import Colib.Topology.HomotopyPullback.Fibration

/-! # The original homotopy-pullback projection of a weak equivalence

All actual fibers are compared by the already constructed homotopy
 equivalences. Their homotopy sets and nonemptiness give the weak property
for the original projection, including components and empty spaces.


Implementation provenance:
`Quillen/Topology/HomotopyFiber/WeakPullback.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace Topology.HomotopyPullback
variable {X A B : Type u} [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace B]

/-- The canonical homotopy-pullback base projection is a weak equivalence
whenever the original pulled-back map is one. -/
theorem baseProjection_isWeakHomotopyEquivalence (f : C(X, B)) (g : C(A, B))
    (hf : IsWeakHomotopyEquivalence f) :
    IsWeakHomotopyEquivalence (baseProjection f g) := by
  apply HomotopyFiber.isWeakHomotopyEquivalence_of_fibers
  · intro a
    exact (HomotopyFiber.nonempty_of_weakEquivalence f hf (g a)).map
      (baseFiberHomotopyEquiv f g a)
  · intro a z n
    let e := (baseFiberHomotopyEquiv f g a).symm
    let := HomotopyFiber.subsingleton_of_weakEquivalence f hf (g a) (e z) n
    exact (homotopyGroupMap_bijective_of_homotopyEquiv e
      (x := z) (y := e z) rfl n).injective.subsingleton

end Topology.HomotopyPullback
