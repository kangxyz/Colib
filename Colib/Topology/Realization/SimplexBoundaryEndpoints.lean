/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.Topology.Realization.SimplexBoundary
public import Mathlib.Tactic.FinCases
public import Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex

/-!
# The two endpoints of the geometric one-simplex boundary

Extracted from the first five declarations of `Quillen/Topology/HELP/IntervalEndpoints.lean`
at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. No HEP result is imported or asserted.
-/
@[expose] public section


noncomputable section

open Convexity
open scoped Topology unitInterval

universe u

namespace Convexity.StdSimplex

attribute [local instance] Classical.propDecidable

/-- The two vertices are all points of the geometric one-simplex boundary. -/
theorem simplexBoundary_one_cases (b : simplexBoundary 1) :
    b.1 = StdSimplex.single 0 ∨ b.1 = StdSimplex.single 1 := by
  have hs : b.1.weights 0 + b.1.weights 1 = 1 := by
    simp
  obtain ⟨i, hi⟩ := b.2
  fin_cases i
  · right
    change b.1.weights 0 = 0 at hi
    have h1 : b.1.weights 1 = 1 := by linarith
    apply StdSimplex.ext
    ext j
    fin_cases j <;> simp [hi, h1]
  · left
    change b.1.weights 1 = 0 at hi
    have h0 : b.1.weights 0 = 1 := by linarith
    apply StdSimplex.ext
    ext j
    fin_cases j <;> simp [hi, h0]

/-- The first interval endpoint as a simplex-boundary point. -/
def boundaryZero : simplexBoundary 1 :=
  ⟨StdSimplex.single 0, ⟨1, by simp⟩⟩

/-- The second interval endpoint as a simplex-boundary point. -/
def boundaryOne : simplexBoundary 1 :=
  ⟨StdSimplex.single 1, ⟨0, by simp⟩⟩

lemma boundaryZero_ne_one : boundaryZero ≠ boundaryOne := by
  intro h
  have h' := congrArg (fun b : simplexBoundary 1 ↦ StdSimplex.homeomorphI b.1) h
  simp [boundaryZero, boundaryOne] at h'

lemma boundary_eq_zero_or_one (b : simplexBoundary 1) : b = boundaryZero ∨ b =
  boundaryOne := by
  rcases simplexBoundary_one_cases b with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)


end Convexity.StdSimplex

attribute [colib_tag "COL-0107",
  colib_ref "HatcherAT" "Chapter 0, simplex coordinate description, page 9"
    "background"
    "The native real one-simplex boundary consists of its two distinct specified vertices"]
  Convexity.StdSimplex.boundaryZero
  Convexity.StdSimplex.boundaryOne
  Convexity.StdSimplex.boundaryZero_ne_one
  Convexity.StdSimplex.boundary_eq_zero_or_one
