/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.StrictWeakTransport
public import Colib.Topology.MappingPath.Map

/-! # Weak invariance of the original homotopy fiber under a strict square

Both total and base maps may change by weak equivalences. Functorial
mapping-path replacement, right properness, and actual strict-fiber
comparison prove the conclusion for the unchanged original fiber map.


Implementation provenance:
`Quillen/Topology/HomotopyFiber/WeakSquareTransport.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace Topology
namespace MappingPath
variable {X Y A B : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace A] [TopologicalSpace B]
  {p : C(X, A)} {q : C(Y, B)} (u : C(X, Y)) (v : C(A, B)) (w : q.comp u = v.comp p)

/-- Functorial mapping-path replacement preserves the original weak total map,
regardless of the map on bases. -/
theorem map_isWeakHomotopyEquivalence (hu : IsWeakHomotopyEquivalence u) :
    IsWeakHomotopyEquivalence (map u v w) := by
  have h : IsWeakHomotopyEquivalence ((map u v w).comp (inclusion p)) := by
    rw [map_inclusion]
    exact (isWeakHomotopyEquivalence_of_homotopyEquiv (inclusionHomotopyEquiv q)).comp hu
  exact h.of_comp_left (isWeakHomotopyEquivalence_of_homotopyEquiv (inclusionHomotopyEquiv p))

/-- With weak total and base maps, the literal strict comparison to the pulled
back endpoint fibration is weak. No cartesian conclusion is assumed. -/
theorem strictComparison_isWeakHomotopyEquivalence
    (hu : IsWeakHomotopyEquivalence u) (hv : IsWeakHomotopyEquivalence v) :
    IsWeakHomotopyEquivalence (strictComparison u v w) :=
  IsWeakHomotopyEquivalence.of_comp_right
    (f := strictComparison u v w)
    (g := HomotopyPullback.strictSourceProjection (endpoint q) v)
    (map_isWeakHomotopyEquivalence u v w hu)
    (HomotopyPullback.strictSourceProjection_isWeakHomotopyEquivalence
      (endpoint q) v (endpoint_homotopyLiftingProperty q) hv)

end MappingPath
namespace HomotopyFiber
variable {X Y A B : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace A] [TopologicalSpace B]
  {p : C(X, A)} {q : C(Y, B)}

/-- A strict square with weak total and base maps induces a weak equivalence
on the original actual homotopy fibers, retaining the source map and complete
postcomposed path exactly. Empty spaces and degree zero are included. -/
theorem map_isWeakHomotopyEquivalence
    (u : C(X, Y)) (v : C(A, B)) (sq : v.comp p = q.comp u)
    (hu : IsWeakHomotopyEquivalence u) (hv : IsWeakHomotopyEquivalence v) (a : A) :
    IsWeakHomotopyEquivalence (map u v sq a) := by
  let e₁ := (MappingPath.endpointFiberHomeomorph p a).symm
  let e₂ := (HomotopyPullback.strictPullbackFiberHomeomorph
    (MappingPath.endpoint q) v a).trans (MappingPath.endpointFiberHomeomorph q (v a))
  have h := (isWeakHomotopyEquivalence_of_homotopyEquiv e₂.toHomotopyEquiv).comp
    ((strictMapOver_isWeakHomotopyEquivalence
      (MappingPath.endpoint p)
      (HomotopyPullback.strictBaseProjection (MappingPath.endpoint q) v)
      (MappingPath.strictComparison u v sq.symm) rfl a
      (MappingPath.endpoint_homotopyLiftingProperty p)
      (HomotopyLiftingProperty.baseChange
        (MappingPath.endpoint q) v (MappingPath.endpoint_homotopyLiftingProperty q))
      (MappingPath.strictComparison_isWeakHomotopyEquivalence u v sq.symm hu hv)).comp
        (isWeakHomotopyEquivalence_of_homotopyEquiv e₁.toHomotopyEquiv))
  exact h

/-- In particular, genuine homotopy equivalences of total and base spaces
transport the original fiber weak equivalence, without choosing based inverses. -/
theorem map_isWeakHomotopyEquivalence_of_equivalences
    (u : ContinuousMap.HomotopyEquiv X Y) (v : ContinuousMap.HomotopyEquiv A B)
    (sq : v.toFun.comp p = q.comp u.toFun) (a : A) :
    IsWeakHomotopyEquivalence (map u.toFun v.toFun sq a) :=
  map_isWeakHomotopyEquivalence u.toFun v.toFun sq
    (isWeakHomotopyEquivalence_of_homotopyEquiv u)
    (isWeakHomotopyEquivalence_of_homotopyEquiv v) a

end HomotopyFiber
end Topology
