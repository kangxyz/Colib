/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module

public import Colib.Analysis.Convex.StdSimplex.Skeleton
public import Colib.Topology.Homotopy.HomotopyGroup.SphericalSimplex

/-!
# Actual increasing faces of a simplex with collapsed geometric skeleton

Adapted from `Quillen/Topology/HomotopyGroups/SphericalFaces.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The map is the actual native
increasing vertex map. The unrelated straightening endpoint is not imported.
-/

@[expose] public noncomputable section

open Convexity
universe u
namespace Topology
variable {Z : Type u} [TopologicalSpace Z] {z : Z} {n : ℕ}

/-- Every increasing face of a simplex with collapsed codimension-two skeleton is spherical. -/
def sphericalFace (τ : C(StdSimplex ℝ (Fin (n + 2)), Z))
    (hτ : ∀ x ∈ StdSimplex.skeleton n (n + 1), τ x = z) (i : Fin (n + 2)) :
    SphericalSimplex Z z n :=
  ⟨τ.comp ⟨StdSimplex.map i.succAbove, StdSimplex.continuous_map ℝ i.succAbove⟩,
    fun x hx ↦ hτ _ ((StdSimplex.map_mem_skeleton_iff i.succAbove
      Fin.succAbove_right_injective x).mpr (StdSimplex.boundary_subset_skeleton n hx))⟩

@[simp] theorem sphericalFace_apply (τ : C(StdSimplex ℝ (Fin (n + 2)), Z))
    (hτ : ∀ x ∈ StdSimplex.skeleton n (n + 1), τ x = z) (i : Fin (n + 2))
    (x : StdSimplex ℝ (Fin (n + 1))) :
    sphericalFace τ hτ i x = τ (StdSimplex.map i.succAbove x) := rfl

end Topology
