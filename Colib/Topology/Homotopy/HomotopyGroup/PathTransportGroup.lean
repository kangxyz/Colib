/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.PathTransport

/-!
# Multiplicativity of the original path transport

The endpoint evaluations on the free path space induce group isomorphisms.
Their composite is exactly the existing path transport, now bundled as a
multiplicative equivalence in every positive degree.
-/

/-! Implementation source: `Quillen/Topology/HomotopyGroups/PathTransportGroup.lean`
at c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual maps, endpoint paths,
universes and signs are retained, with native Colib dependencies. -/
@[expose] public section

noncomputable section

universe u

namespace Topology

variable {X : Type u} [TopologicalSpace X] {x y : X}

/-- The original path transport as an actual isomorphism of positive homotopy groups. -/
def pathTransportMulEquiv (γ : Path x y) (n : ℕ) :
    HomotopyGroup.Pi (n + 1) X x ≃* HomotopyGroup.Pi (n + 1) X y :=
  (MulEquiv.ofBijective (HomotopyGroup.piMap n (freePathEvaluation X 0) γ.source)
    (homotopyGroupMap_bijective_of_homotopyEquiv
      (freePathEvaluationHomotopyEquiv X 0) γ.source (n + 1))).symm.trans
    (MulEquiv.ofBijective (HomotopyGroup.piMap n (freePathEvaluation X 1) γ.target)
      (homotopyGroupMap_bijective_of_homotopyEquiv
        (freePathEvaluationHomotopyEquiv X 1) γ.target (n + 1)))

@[simp]
lemma pathTransportMulEquiv_apply (γ : Path x y) (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) X x) :
    pathTransportMulEquiv γ n a = pathTransport γ (n + 1) a := rfl

end Topology
