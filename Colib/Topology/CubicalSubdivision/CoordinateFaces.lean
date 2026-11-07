/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.CubicalSubdivision.FaceBoundary

/-!
# Original coordinate sections as unions of actual grid faces

Each point on a specified grid-coordinate section belongs to a whole face in that same section.
In particular, every outer coordinate face is controlled by the all-incident chart invariant;
this retains the original path endpoints and the whole stationary boundary of a cube family.
-/

/-! Implementation provenance: adapted from
`Quillen/Topology/CubicalSubdivision/CoordinateFaces.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, finite bounds,
whole path families and universe parameters are retained in their native owners. -/
@[expose] public section

noncomputable section
open Topology TopCat

open scoped Topology unitInterval

namespace Topology.CubicalSubdivision

/-- An original coordinate section is covered by whole grid faces within that same section. -/
theorem exists_face_in_coordinate_vertex (n mesh : ℕ) (i : Fin n) (j : Fin (mesh + 2))
    (x : Cube n) (hx : x i = gridVertex mesh j) :
    ∃ G : FaceIndex n mesh, ∃ s : Active G → unitInterval,
      face G s = x ∧ ∀ t, face G t i = gridVertex mesh j := by
  obtain ⟨k, v, hv⟩ := cell_covers n mesh x
  let F := maximalFace k
  let a : Active F := ⟨i, k i, rfl⟩
  let t : Active F → unitInterval := fun z ↦ v z.val
  have ht : face F t = x := (maximalFace_apply k v).trans hv
  have hi : face F t i = gridVertex mesh j := (congrFun ht i).trans hx
  refine ⟨fixedFace F a j, t ∘ fixedFaceActiveEmbedding F a j,
    (face_fixedFace F a j t hi).trans ht, ?_⟩
  intro s
  exact face_fixed _ s i j (Function.update_self _ _ _)

/-- The first outer coordinate face is a union of unchanged original grid faces. -/
theorem exists_face_in_coordinate_zero (n mesh : ℕ) (i : Fin n)
    (x : Cube n) (hx : x i = 0) :
    ∃ G : FaceIndex n mesh, ∃ s : Active G → unitInterval,
      face G s = x ∧ ∀ t, face G t i = 0 := by
  have hzero : gridVertex mesh 0 = 0 := by
    apply Subtype.ext
    simp only [gridVertex, Fin.val_zero, Nat.cast_zero, zero_div]
    rfl
  obtain ⟨G, s, hG, hs⟩ := exists_face_in_coordinate_vertex n mesh i 0 x (hx.trans hzero.symm)
  exact ⟨G, s, hG, fun t ↦ (hs t).trans hzero⟩

/-- The last outer coordinate face is covered in the same literal coordinates. -/
theorem exists_face_in_coordinate_one (n mesh : ℕ) (i : Fin n)
    (x : Cube n) (hx : x i = 1) :
    ∃ G : FaceIndex n mesh, ∃ s : Active G → unitInterval,
      face G s = x ∧ ∀ t, face G t i = 1 := by
  have hone : gridVertex mesh (Fin.last (mesh + 1)) = 1 := by
    apply Subtype.ext
    change (((mesh + 1 : ℕ) : ℝ) / (mesh + 1)) = 1
    rw [Nat.cast_add, Nat.cast_one, div_self (by positivity : (mesh : ℝ) + 1 ≠ 0)]
  obtain ⟨G, s, hG, hs⟩ := exists_face_in_coordinate_vertex n mesh i (Fin.last (mesh + 1)) x
    (hx.trans hone.symm)
  exact ⟨G, s, hG, fun t ↦ (hs t).trans hone⟩

end Topology.CubicalSubdivision
