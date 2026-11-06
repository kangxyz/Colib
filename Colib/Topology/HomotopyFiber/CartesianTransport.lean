/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.StrictWeakTransport
public import Colib.Topology.MappingPath.Map

/-!
# Actual homotopy fibers of a weakly cartesian square

Weakness of the original constant-path comparison suffices to make the
functorial mapping-path strict comparison weak. The two endpoint projections
are genuine fibrations, so their actual strict fibers give the unchanged
original homotopy-fiber map. No weakness of the map on bases is required.


Implementation provenance:
`Quillen/Topology/HomotopyFiber/CartesianTransport.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section


noncomputable section
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

namespace Topology
namespace MappingPath

variable {X Y A B : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace A] [TopologicalSpace B]
  {p : C(X, A)} {q : C(Y, B)} (u : C(X, Y)) (v : C(A, B))
  (w : q.comp u = v.comp p)

/-- A weakly cartesian square becomes the actual weak comparison to the
strict pullback of mapping-path endpoint fibrations. -/
theorem strictComparison_isWeakHomotopyEquivalence_of_comparison
    (h : IsWeakHomotopyEquivalence (HomotopyPullback.comparison q v p u w)) :
    IsWeakHomotopyEquivalence (strictComparison u v w) := by
  have h' : IsWeakHomotopyEquivalence
      ((strictPullbackHomeomorph (q := q) v).toHomotopyEquiv.toFun.comp
        ((strictComparison u v w).comp (inclusion p))) := by
    convert h using 1
    ext x
    rfl
  exact (h'.of_comp_right
    (isWeakHomotopyEquivalence_of_homotopyEquiv
      (strictPullbackHomeomorph (q := q) v).toHomotopyEquiv)).of_comp_left
        (isWeakHomotopyEquivalence_of_homotopyEquiv (inclusionHomotopyEquiv p))

end MappingPath
namespace HomotopyFiber

variable {X Y A B : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace A] [TopologicalSpace B]
  {p : C(X, A)} {q : C(Y, B)}

/-- The original fiber map of a weakly cartesian square is weak over every
point of the original base, retaining the source point and complete path. -/
theorem map_isWeakHomotopyEquivalence_of_comparison
    (u : C(X, Y)) (v : C(A, B)) (sq : v.comp p = q.comp u)
    (h : IsWeakHomotopyEquivalence (HomotopyPullback.comparison q v p u sq.symm))
    (a : A) : IsWeakHomotopyEquivalence (map u v sq a) := by
  let e₁ := (MappingPath.endpointFiberHomeomorph p a).symm
  let e₂ := (HomotopyPullback.strictPullbackFiberHomeomorph
    (MappingPath.endpoint q) v a).trans (MappingPath.endpointFiberHomeomorph q (v a))
  exact (isWeakHomotopyEquivalence_of_homotopyEquiv e₂.toHomotopyEquiv).comp
    ((strictMapOver_isWeakHomotopyEquivalence
      (MappingPath.endpoint p)
      (HomotopyPullback.strictBaseProjection (MappingPath.endpoint q) v)
      (MappingPath.strictComparison u v sq.symm) rfl a
      (MappingPath.endpoint_homotopyLiftingProperty p)
      (HomotopyLiftingProperty.baseChange
        (MappingPath.endpoint q) v (MappingPath.endpoint_homotopyLiftingProperty q))
      (MappingPath.strictComparison_isWeakHomotopyEquivalence_of_comparison u v sq.symm h)).comp
        (isWeakHomotopyEquivalence_of_homotopyEquiv e₁.toHomotopyEquiv))

end HomotopyFiber
end Topology
