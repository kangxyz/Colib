/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.MetricOrderComplex.SimplexCoordinates
public import Colib.Topology.Realization.DescAcross
public import Colib.Topology.ClassifyingSpace.Basic

/-!
# The actual barycentric coordinate map from poset realization

The compatible finite-chain charts descend through the original geometric
realization colimit. The resulting continuous map retains the exact original
simplex weights and every vertex. Its target has the finite-support L1 metric;
no weak-to-strong homotopy equivalence is assumed or asserted here.
-/

/-! Implementation source: `Quillen/Topology/MetricOrderComplex/RealizationCoordinates.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The pinned native realization and
its standard-simplex coordinates are unchanged. -/
@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Convexity SSet Opposite
open scoped Simplicial Topology

universe u

namespace Topology.MetricOrderComplex

variable {P : Type u} [PartialOrder P]

/-- Aggregate the barycentric coordinates of the actual nerve realization. -/
def realizationCoordinates : C(|nerve P|, MetricOrderComplex P) :=
  realizationDesc (fun _ s ↦ simplexCoordinates s) (fun a s t ↦
    simplexCoordinates_naturality a s t)

/-- The coordinate map evaluates on each original simplex without changing its model. -/
@[simp]
theorem realizationCoordinates_simplex {n : SimplexCategory} (s : (nerve P).obj (op n))
    (t : StdSimplex ℝ (Fin (n.len + 1))) :
    realizationCoordinates (realizationSimplex s t) = simplexCoordinates s t :=
  realizationDesc_simplex _ _ n s t

/-- Coordinates at repeated vertices are added by the actual finite sum of vertex weights. -/
theorem realizationCoordinates_simplex_weights {n : SimplexCategory}
    (s : (nerve P).obj (op n)) (t : StdSimplex ℝ (Fin (n.len + 1))) :
    (realizationCoordinates (realizationSimplex s t)).weights =
      ∑ i, Finsupp.single (s.obj i) (t.weights i) := by
  rw [realizationCoordinates_simplex, simplexCoordinates_weights]

/-- Every original classifying-space vertex is sent to its mass-one coordinate vector. -/
@[simp]
theorem realizationCoordinates_vertex (p : P) :
    realizationCoordinates (classifyingSpacePoint.{u, u} p) = vertex p := by
  rw [show classifyingSpacePoint.{u, u} p =
    realizationSimplex (ComposableArrows.mk₀ p) (StdSimplex.single 0) by
      rw [realizationSimplex_zero]; rfl]
  rw [realizationCoordinates_simplex, simplexCoordinates_single]
  rfl

end Topology.MetricOrderComplex
