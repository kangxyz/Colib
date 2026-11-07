/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Homotopy.OpenCover.Refinement

/-!
# Subdivision

A finite actual affine subdivision, with a containing chart for each edge.
Monotonicity is retained for geometric refinement, although local collapse is stronger.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Set
universe u v w z
namespace FundamentalGroupoid.OpenCover
variable {X : Type u} [TopologicalSpace X] {ι : Type v}
variable {C : Type w} [Category.{z} C] {U : ι → Set X}

/-- A finite actual affine subdivision, with a containing chart for each edge.
Monotonicity is retained for geometric refinement, although local collapse is stronger. -/
structure PathSubdivision {x y : X} (p : Path x y) where
  /-- The number of path segments. -/
  n : ℕ
  /-- The ordered subdivision parameters, including both endpoints. -/
  times : Fin (n + 1) → unitInterval
  monotone : Monotone times
  first : times 0 = 0
  last : times (Fin.last n) = 1
  /-- A containing chart for each closed path segment. -/
  chart : Fin n → ι
  contained : ∀ j, Set.range (p.subpath (times j.castSucc) (times j.succ)) ⊆ U (chart j)

namespace PathSubdivision
variable {x y : X} {p : Path x y} (s : PathSubdivision (U := U) p)

/-- The ordered local values, transported to the actual original endpoints. -/
def value (d : ChartData (C := C) U) : d.obj x ⟶ d.obj y :=
  eqToHom (congrArg d.obj ((congrArg p s.first).trans p.source).symm) ≫
    finiteChainComp (fun j => d.obj (p (s.times j)))
      (fun j => d.localValue (s.chart j)
        (p.subpath (s.times j.castSucc) (s.times j.succ)) (s.contained j)) ≫
    eqToHom (congrArg d.obj ((congrArg p s.last).trans p.target))

/-- Every such refinement of a local path has its original local value. -/
theorem value_eq_localValue (d : ChartData (C := C) U) (hc : d.Compatible)
    (i : ι) (hp : Set.range p ⊆ U i) : s.value d = d.localValue i p hp :=
  d.localValue_refinement hc i p hp s.times s.first s.last s.chart s.contained

end PathSubdivision

namespace ChartData
variable (d : ChartData (C := C) U)

/-- Two independently chosen finite refinements of every coarse path in a
finite chart-contained chain have the same ordered value. Coarse charts may
vary, as may all fine charts, subdivision lengths and breakpoints. This theorem
uses actual overlap-path compatibility, with no global decoder hypothesis. -/
theorem blockRefinement_independent (hc : d.Compatible) {n : ℕ}
    (x : Fin (n + 1) → X) (p : ∀ j : Fin n, Path (x j.castSucc) (x j.succ))
    (i : Fin n → ι) (hp : ∀ j, Set.range (p j) ⊆ U (i j))
    (s t : ∀ j, PathSubdivision (U := U) (p j)) :
    finiteChainComp (fun j => d.obj (x j)) (fun j => (s j).value d) =
      finiteChainComp (fun j => d.obj (x j)) (fun j => (t j).value d) := by
  have he : (fun j => (s j).value d) = (fun j => (t j).value d) := by
    funext j
    exact ((s j).value_eq_localValue d hc (i j) (hp j)).trans
      ((t j).value_eq_localValue d hc (i j) (hp j)).symm
  rw [he]

end ChartData
end FundamentalGroupoid.OpenCover
