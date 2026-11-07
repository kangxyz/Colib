/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.Topology.Homotopy.HomotopyGroup.PathTransportComposition
public import Colib.Topology.Homotopy.HomotopyGroup.MovingBasepoint
/-!
Implementation provenance:
`Quillen/Topology/HomotopyGroups/BasedMapNaturality.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Based naturality from an original square and its exact track coherence

An unbased homotopy square alone need not commute on fixed-basepoint homotopy
groups. The endpoint-fixed coherence of its actual point paths is retained as
an explicit hypothesis. It yields equality of the original corrected maps in
every finite degree, without discarding fundamental-group actions.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v u' v'
namespace Topology
variable {X : Type u} {Y : Type v} {X' : Type u'} {Y' : Type v'}
  [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace X'] [TopologicalSpace Y']

/-- The corrected homotopy maps commute when the complete basepoint tracks agree
up to an endpoint-fixed path homotopy. -/
theorem homotopyGroupMap_based_square
    (f : C(X, Y)) (g : C(X', Y')) (a : C(X, X')) (b : C(Y, Y'))
    (H : (b.comp f).Homotopy (g.comp a))
    (x : X) (x' : X') (y : Y) (y' : Y')
    (pf : Path (f x) y) (pg : Path (g x') y')
    (pa : Path (a x) x') (pb : Path (b y) y')
    (hpath : ((pf.map b.continuous).trans pb).Homotopic
      ((H.evalAt x).trans ((pa.map g.continuous).trans pg)))
    (n : ℕ) (α : HomotopyGroup.Pi n X x) :
    pathTransport pb n (HomotopyGroup.map b rfl
      (pathTransport pf n (HomotopyGroup.map f rfl α))) =
    pathTransport pg n (HomotopyGroup.map g rfl
      (pathTransport pa n (HomotopyGroup.map a rfl α))) := by
  rw [← pathTransport_naturality b pf n,
    ← pathTransport_trans (pf.map b.continuous) pb n,
    pathTransport_eq_of_homotopic hpath n,
    pathTransport_trans,
    ← HomotopyGroup.map_comp f rfl b rfl]
  refine (congrArg (pathTransport ((pa.map g.continuous).trans pg) n)
    (pathTransport_homotopyGroupMap_homotopy H x n α)).trans ?_
  rw [HomotopyGroup.map_comp a rfl g rfl, pathTransport_trans,
    pathTransport_naturality g pa n]
end Topology
