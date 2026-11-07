/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.Cube.StickBreakingFaces
public import Colib.Topology.Homotopy.Cube.CoordinateFaceFold
public import Colib.Topology.Homotopy.HomotopyGroup.SphericalFaces

/-!
# The explicit quotient carries the cubical codimension-two skeleton correctly

The lower faces and the final upper face retain their increasing simplex
parameters. All other upper faces have two zero weights. These literal
formulas imply the required skeleton condition, without treating the
stick-breaking quotient as a homeomorphism.
-/

/-! Implementation source: `Quillen/Topology/Cube/StickBreakingSkeleton.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Native function-subtype coordinates
and the actual ordered stick-breaking quotient are used throughout. -/
@[expose] public section
noncomputable section
open Topology
open scoped Topology unitInterval

namespace Topology

/-- Deleting one endpoint coordinate leaves the other endpoint on the cube boundary. -/
theorem removeNth_mem_cubeBoundary {n : ℕ} (x : Fin (n + 1) → I)
    (i j : Fin (n + 1)) (hij : i ≠ j) (hj : x j = 0 ∨ x j = 1) :
    i.removeNth x ∈ _root_.Cube.boundary (Fin n) := by
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij.symm
  exact ⟨k, by simpa only [Fin.removeNth_apply, hk] using hj⟩

end Topology

namespace Cube

/-- The nonfinal upper faces land in the genuine simplex skeleton in all dimensions. -/
theorem stickBreaking_upper_mem_skeleton {n : ℕ} (j : Fin (n + 1))
    (hj : j.val < n) (t : Fin n → I) :
    stickBreaking (n + 1) (j.insertNth 1 t) ∈ stdSimplex.skeleton n (n + 1) := by
  obtain ⟨i, k, hik, hi, hk⟩ := stickBreaking_upper_two_zero j hj t
  exact stdSimplex.mem_skeleton_of_two_zero _ i k hik hi hk

/-- The terminal cubical codimension-two boundary is carried into the
actual geometric simplex codimension-two skeleton. -/
theorem stickBreaking_codimTwo_mem_skeleton {n : ℕ} (x : Fin (n + 1) → I)
    (hx : x ∈ cubeCodimTwoBoundary (Fin (n + 1))) :
    stickBreaking (n + 1) x ∈ stdSimplex.skeleton n (n + 1) := by
  obtain ⟨i, j, hij, hi, hj⟩ := hx
  have hb := removeNth_mem_cubeBoundary x i j hij hj
  have hs : stickBreaking n (i.removeNth x) ∈ stdSimplex.skeleton n n :=
    stdSimplex.boundary_subset_skeleton n ((stickBreaking_mem_boundary_iff n _).mpr hb)
  rcases hi with hi | hi
  · have hx : i.insertNth 0 (i.removeNth x) = x := by
      simpa only [hi] using (Fin.insertNth_self_removeNth i x)
    rw [← hx, stickBreaking_lower_face]
    exact (stdSimplex.map_mem_skeleton_iff i.castSucc.succAbove
      Fin.succAbove_right_injective _).mpr hs
  · have hx : i.insertNth 1 (i.removeNth x) = x := by
      simpa only [hi] using (Fin.insertNth_self_removeNth i x)
    by_cases hilast : i = Fin.last n
    · subst i
      rw [← hx, Fin.insertNth_last', stickBreaking_upper_last]
      exact (stdSimplex.map_mem_skeleton_iff (Fin.last (n + 1)).succAbove
        Fin.succAbove_right_injective _).mpr hs
    · rw [← hx]
      exact stickBreaking_upper_mem_skeleton i (by
        have hine : i.val ≠ n := by intro h; apply hilast; exact Fin.ext h
        omega) _

end Cube
