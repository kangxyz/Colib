/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.ContractibleBase
public import Colib.Topology.HomotopyFiber.StrictWeakTransport
public import Colib.Topology.HELP.TwoOfThree

/-! # Fiber compact HELP detects the total map over a contracted base

The original fiber projections are genuine equivalences. Proved HELP
composition and cancellation therefore give the original total-map
lifting property. This requires an actual base contraction and does not
supply gluing over a general base or compatible relative face lifts.


Implementation provenance:
`Quillen/Topology/HomotopyFiber/ContractibleBaseHELP.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
universe u
namespace Topology.HomotopyFiber
variable {E F B : Type u} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]

/-- Over a genuinely contracted base, compact HELP on the original actual
homotopy-fiber map gives compact HELP on the original total map. -/
theorem compactHELP_of_fiber_contraction
    (p : C(E, B)) (q : C(F, B)) (f : C(E, F)) (sq : q.comp f = p)
    (b : B) (H : (ContinuousMap.id B).Homotopy (ContinuousMap.const B b))
    (hf : CompactHomotopyExtensionLiftingProperty (mapOver p q f sq b)) :
    CompactHomotopyExtensionLiftingProperty f := by
  have hj₁ : CompactHomotopyExtensionLiftingProperty (projection p b) :=
    compactHELP_of_homotopyEquiv (projectionEquivOfContraction p b H)
  have hj₂ : CompactHomotopyExtensionLiftingProperty (projection q b) :=
    compactHELP_of_homotopyEquiv (projectionEquivOfContraction q b H)
  have h : CompactHomotopyExtensionLiftingProperty (f.comp (projection p b)) :=
    hj₂.comp hf
  exact h.cancel_first hj₁

/-- The strict-fiber form applies to actual Hurewicz fibrations, with both
original inclusion maps supplied by genuine homotopy equivalences. -/
theorem compactHELP_of_strictFiber_contraction
    (p : C(E, B)) (q : C(F, B)) (f : C(E, F)) (sq : q.comp f = p)
    (hp : HomotopyLiftingProperty p) (hq : HomotopyLiftingProperty q)
    (b : B) (H : (ContinuousMap.id B).Homotopy (ContinuousMap.const B b))
    (hf : CompactHomotopyExtensionLiftingProperty (strictMapOver p q f sq b)) :
    CompactHomotopyExtensionLiftingProperty f := by
  have hj₁ : CompactHomotopyExtensionLiftingProperty (strictFiberToSource p b) :=
    compactHELP_of_homotopyEquiv (strictFiberEquivOfContraction p hp b H)
  have hj₂ : CompactHomotopyExtensionLiftingProperty (strictFiberToSource q b) :=
    compactHELP_of_homotopyEquiv (strictFiberEquivOfContraction q hq b H)
  have h : CompactHomotopyExtensionLiftingProperty (f.comp (strictFiberToSource p b)) :=
    hj₂.comp hf
  exact h.cancel_first hj₁

end Topology.HomotopyFiber
