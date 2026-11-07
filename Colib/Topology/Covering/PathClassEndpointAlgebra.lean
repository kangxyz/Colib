/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Covering.PathClassPrebundle

/-!
# Endpoint algebra for the literal path-class total space

This algebra retains both arbitrary chart offsets. The actual constant-coordinate
premise is proved in `PathClassEndpoint` from the chart-generated topology.
The neutral total point need not have neutral chart coordinate.
-/
/-! Implementation source: `Quillen/Topology/Covering/PathClassEndpointAlgebra.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual topologies,
path classes, dependent endpoint equalities and covering maps are retained. -/
@[expose] public section
noncomputable section
universe u
namespace Topology.PathThinNeighborhoods
variable {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
  (A : PathThinNeighborhoods X) (b : X)

/-- The exact chronological endpoint class after an original path class. -/
def endpointAction {x y : X} (r : PathClassFiber b x)
    (q : Path.Homotopic.Quotient x y) : PathClassFiber b y :=
  PathClassFiber.ofQuotient (r.toQuotient.trans q)

omit [PathConnectedSpace X] in
/-- Constant paths leave the literal fiber element unchanged. -/
theorem endpointAction_refl {x : X} (r : PathClassFiber b x) :
    endpointAction b r (.refl x) = r := by
  apply PathClassFiber.ext
  simp [endpointAction]

omit [PathConnectedSpace X] in
/-- Successive transport follows chronological path composition. -/
theorem endpointAction_trans {x y z : X} (r : PathClassFiber b x)
    (q : Path.Homotopic.Quotient x y) (q' : Path.Homotopic.Quotient y z) :
    endpointAction b (endpointAction b r q) q' = endpointAction b r (q.trans q') := by
  apply PathClassFiber.ext
  exact Path.Homotopic.Quotient.trans_assoc _ _ _

/-- Equal actual chart coordinates imply the exact endpoint action for a path
inside that chart. The offset chart classes occur on both sides and cancel. -/
theorem endpointAction_eq_of_fiberEquiv_eq (c : X) {x y : X}
    (hx : x ∈ A.neighborhood c) (hy : y ∈ A.neighborhood c)
    (p : Path x y) (hp : ∀ t, p t ∈ A.neighborhood c)
    (r : PathClassFiber b x) (s : PathClassFiber b y)
    (hcoord : A.fiberEquiv b c x r = A.fiberEquiv b c y s) :
    endpointAction b r (.mk p) = s := by
  have heq := congrArg PathClassFiber.toQuotient hcoord
  change r.toQuotient.trans (A.chartClass b c x).symm =
    s.toQuotient.trans (A.chartClass b c y).symm at heq
  have hc := A.chartClass_trans b c hx hy p hp
  apply PathClassFiber.ext
  change r.toQuotient.trans (.mk p) = s.toQuotient
  calc
    r.toQuotient.trans (.mk p) =
        (r.toQuotient.trans (A.chartClass b c x).symm).trans
          ((A.chartClass b c x).trans (.mk p)) := by
      rw [Path.Homotopic.Quotient.trans_assoc,
        ← Path.Homotopic.Quotient.trans_assoc (A.chartClass b c x).symm]
      simp
    _ = (s.toQuotient.trans (A.chartClass b c y).symm).trans
          (A.chartClass b c y) := by rw [heq, hc]
    _ = s.toQuotient := by simp

end Topology.PathThinNeighborhoods
