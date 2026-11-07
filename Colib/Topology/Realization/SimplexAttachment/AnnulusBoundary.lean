/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Realization.SimplexAnnulus
public import Colib.Topology.Realization.SimplexBoundaryEndpoints

/-!
# Annulus Boundary

The actual geometric overlap projects radially to its simplex boundary.
-/

@[expose] public section

noncomputable section
open Set CategoryTheory _root_.stdSimplex
namespace TopCat.SimplexAttachment

/-- The actual geometric overlap projects radially to its simplex boundary. -/
def annulusBoundary (n : ℕ) : C(simplexAnnulus n, _root_.stdSimplex.boundary n) :=
  (simplexBoundaryCollarRetraction n).comp
    ⟨fun x => ⟨x.val, x.property.1⟩, by fun_prop⟩

/-- The one-simplex boundary has precisely its two specified geometric vertices. -/
theorem finite_boundary_one : Finite (_root_.stdSimplex.boundary 1) := by
  apply Finite.of_surjective (fun b : Bool => if b then boundaryZero else boundaryOne)
  intro x
  rcases boundary_eq_zero_or_one x with h | h
  · exact ⟨true, by simpa using h.symm⟩
  · exact ⟨false, by simpa using h.symm⟩

/-- Every actual path in the geometric one-cell overlap stays on the same
boundary side. This distinguishes the two sides even for a loop edge whose
attaching map identifies its endpoints in the old space. -/
theorem annulusBoundary_one_path_constant {a b : simplexAnnulus 1}
    (p : Path a b) (t : unitInterval) : annulusBoundary 1 (p t) = annulusBoundary 1 a := by
  let : Finite (_root_.stdSimplex.boundary 1) := finite_boundary_one
  have he := TotallyDisconnectedSpace.eq_of_continuous
    (fun t => annulusBoundary 1 (p t)) ((annulusBoundary 1).continuous.comp p.continuous) t 0
  simpa using he

end TopCat.SimplexAttachment
