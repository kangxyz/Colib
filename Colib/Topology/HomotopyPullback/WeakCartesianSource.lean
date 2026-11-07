/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyPullback.WeakSource

/-!
# Canonical weak cartesian comparisons under change of total source

A weak map of total sources over a common base induces the original weak
map of homotopy pullbacks, retaining the full parameter and path. The exact
comparison triangle transports weak cartesianness back to the original
square. Neither an inverse map nor a fibration of total sources is needed.


Implementation provenance:
`Quillen/Topology/HomotopyPullback/WeakCartesianSource.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section


noncomputable section
open Topology TopCat
open scoped Topology unitInterval
universe u
namespace Topology.HomotopyPullback

variable {X Y A B Z : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace Z]

/-- Transport the weak canonical comparison through an actual weak source
map over the base and its exact endpoint triangle. -/
theorem comparison_isWeakHomotopyEquivalence_of_sourceMap
    (p : C(X, B)) (q : C(Y, B)) (k : C(A, B))
    (r : C(Z, A)) (f : C(Z, X)) (g : C(Z, Y))
    (commP : p.comp f = k.comp r) (commQ : q.comp g = k.comp r)
    (e : C(X, Y)) (he : IsWeakHomotopyEquivalence e)
    (hover : q.comp e = p) (htriangle : e.comp f = g)
    (h : IsWeakHomotopyEquivalence (comparison q k r g commQ)) :
    IsWeakHomotopyEquivalence (comparison p k r f commP) := by
  subst p
  have ht : (sourceMap k q e).comp (comparison (q.comp e) k r f commP) =
      comparison q k r g commQ := by
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    change (r z,e (f z),ContinuousMap.const unitInterval (k (r z))) =
      (r z,g z,ContinuousMap.const unitInterval (k (r z)))
    exact Prod.ext rfl (Prod.ext (ContinuousMap.congr_fun htriangle z) rfl)
  have hw : IsWeakHomotopyEquivalence
      ((sourceMap k q e).comp (comparison (q.comp e) k r f commP)) := by
    rw [ht]
    exact h
  exact hw.of_comp_right (sourceMap_isWeakHomotopyEquivalence k q e he)

end Topology.HomotopyPullback
