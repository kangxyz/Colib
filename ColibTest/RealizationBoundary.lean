/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.Topology.Realization.Boundary

/-! Isolated, uncompiled actual-map obligations. -/
@[expose] public noncomputable section
open CategoryTheory Convexity.StdSimplex
open scoped Simplicial Topology
universe u
namespace SSet

example (n : ℕ) (x : |(∂Δ[n] : SSet.{u})|) :
    (realizationBoundaryComparison n x).1 =
      SimplexCategory.toTopHomeo ⦋n⦌ (SSet.toTop.map ∂Δ[n].ι x) := rfl

example {n : ℕ} (i : Fin (n + 2)) (t : |(Δ[n] : SSet.{u})|) :
    realizationBoundaryCoordinates (n + 1) (realizationBoundaryFace i t) =
      Convexity.StdSimplex.map i.succAbove (SimplexCategory.toTopHomeo ⦋n⦌ t) :=
  realizationBoundaryCoordinates_face i t

example (n : ℕ) (x : |(∂Δ[n] : SSet.{u})|) :
    realizationBoundaryHomeomorph n x = realizationBoundaryComparison n x := rfl

example (n : ℕ) : Function.Bijective (realizationBoundaryComparison.{u} n) :=
  ⟨realizationBoundaryComparison_injective n, realizationBoundaryComparison_surjective n⟩

example : IsEmpty |(∂Δ[0] : SSet.{u})| := inferInstance
example : IsEmpty (Convexity.StdSimplex.boundary 0) := inferInstance
example (n : ℕ) : CompactSpace |(∂Δ[n] : SSet.{u})| := inferInstance
example (n : ℕ) : T2Space |(∂Δ[n] : SSet.{u})| := inferInstance
example (n : ℕ) : LocallyCompactSpace |(∂Δ[n] : SSet.{u})| := inferInstance

end SSet

#print axioms SSet.realizationBoundaryComparison_injective
#print axioms SSet.realizationBoundaryHomeomorph
#print axioms SSet.realizationBoundary_locallyCompactSpace
