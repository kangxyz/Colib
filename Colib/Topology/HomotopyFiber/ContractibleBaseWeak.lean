/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.ContractibleBase
public import Colib.Topology.HELP.StrictPullback
public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalenceCancellation

/-! # Original weak maps over contracted bases

Genuine strict-fiber inclusion equivalences and actual pullback fiber
homeomorphisms transfer the complete empty-aware weak property. No HELP
property on arbitrary compact pairs is inferred.


Implementation provenance:
`Quillen/Topology/HomotopyFiber/ContractibleBaseWeak.lean`
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

/-- The original total map is weak when its actual strict-fiber map is
weak over an explicitly contracted base of genuine fibrations. -/
theorem weak_of_strictFiber_contraction
    (p : C(E, B)) (q : C(F, B)) (f : C(E, F)) (sq : q.comp f = p)
    (hp : HomotopyLiftingProperty p) (hq : HomotopyLiftingProperty q)
    (b : B) (H : (ContinuousMap.id B).Homotopy (ContinuousMap.const B b))
    (hf : IsWeakHomotopyEquivalence (strictMapOver p q f sq b)) :
    IsWeakHomotopyEquivalence f := by
  have h₁ := isWeakHomotopyEquivalence_of_homotopyEquiv (strictFiberEquivOfContraction p hp b H)
  have h₂ := isWeakHomotopyEquivalence_of_homotopyEquiv (strictFiberEquivOfContraction q hq b H)
  have h : IsWeakHomotopyEquivalence (f.comp (strictFiberToSource p b)) := h₂.comp hf
  exact h.of_comp_left h₁

end Topology.HomotopyFiber
namespace Topology.HomotopyPullback
variable {E F B D : Type u}
    [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B] [TopologicalSpace D]

/-- Literal strict pullback maps retain the original fiber weak equivalence
under the genuine fiber homeomorphisms. -/
theorem strictPullbackMapOver_fiber_weak
    (p : C(E, B)) (q : C(F, B)) (f : C(E, F)) (sq : q.comp f = p)
    (r : C(D, B)) (d : D)
    (hf : IsWeakHomotopyEquivalence (HomotopyFiber.strictMapOver p q f sq (r d))) :
    IsWeakHomotopyEquivalence
      (HomotopyFiber.strictMapOver (strictBaseProjection p r) (strictBaseProjection q r)
        (strictPullbackMapOver p q f sq r) rfl d) := by
  have h₁ := isWeakHomotopyEquivalence_of_homotopyEquiv
    (strictPullbackFiberHomeomorph p r d).toHomotopyEquiv
  have h₂ := isWeakHomotopyEquivalence_of_homotopyEquiv
    (strictPullbackFiberHomeomorph q r d).toHomotopyEquiv
  have h : IsWeakHomotopyEquivalence
      ((strictPullbackFiberHomeomorph q r d).toHomotopyEquiv.toFun.comp
        (HomotopyFiber.strictMapOver (strictBaseProjection p r) (strictBaseProjection q r)
          (strictPullbackMapOver p q f sq r) rfl d)) := by
    rw [strictPullbackFiberHomeomorph_naturality]
    exact hf.comp h₁
  exact h.of_comp_right h₂

end Topology.HomotopyPullback
