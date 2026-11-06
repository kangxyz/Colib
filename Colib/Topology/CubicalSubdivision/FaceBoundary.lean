/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.CubicalSubdivision.FaceComplex

/-! # Whole boundaries lie in the lower actual grid skeleton

Implementation provenance:
`Quillen/Topology/CubicalSubdivision/FaceBoundary.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
open scoped Topology unitInterval
namespace Topology.CubicalSubdivision

/-- Replace one moving coordinate by an actual grid vertex. -/
def fixedFace {n m : ℕ} (F : FaceIndex n m) (i : Active F) (j : Fin (m + 2)) :
    FaceIndex n m := Function.update F i.1 (Sum.inl j)

theorem fixedFace_active_ne {n m : ℕ} (F : FaceIndex n m) (i : Active F)
    (j : Fin (m + 2)) (a : Active (fixedFace F i j)) : a.1 ≠ i.1 := by
  intro h
  obtain ⟨k,hk⟩ := a.2
  simp only [fixedFace,h,Function.update_self] at hk
  cases hk

/-- The remaining moving coordinates embed into the original set, omitting
exactly the coordinate that was fixed. -/
def fixedFaceActiveEmbedding {n m : ℕ} (F : FaceIndex n m) (i : Active F)
    (j : Fin (m + 2)) : Active (fixedFace F i j) ↪ Active F where
  toFun a := ⟨a.1,by
    obtain ⟨k,hk⟩ := a.2
    exact ⟨k, by simpa only [fixedFace,Function.update_of_ne (fixedFace_active_ne F i j a)]
      using hk⟩⟩
  inj' a b h := Subtype.ext (congrArg (fun z : Active F ↦ z.1) h)

@[simp] theorem fixedFaceActiveEmbedding_val {n m : ℕ} (F : FaceIndex n m)
    (i : Active F) (j : Fin (m + 2)) (a : Active (fixedFace F i j)) :
    (fixedFaceActiveEmbedding F i j a).1 = a.1 := rfl

theorem fixedFace_dimension_lt {n m : ℕ} (F : FaceIndex n m) (i : Active F)
    (j : Fin (m + 2)) : faceDimension (fixedFace F i j) < faceDimension F := by
  apply Fintype.card_lt_of_injective_of_notMem (fixedFaceActiveEmbedding F i j)
    (fixedFaceActiveEmbedding F i j).injective (b := i)
  rintro ⟨a,ha⟩
  exact fixedFace_active_ne F i j a (congrArg Subtype.val ha)

/-- Fixing a coordinate already at the indicated grid vertex preserves the
entire original point, with the remaining parameter coordinates unchanged. -/
theorem face_fixedFace {n m : ℕ} (F : FaceIndex n m) (i : Active F)
    (j : Fin (m + 2)) (t : Active F → unitInterval)
    (ht : face F t i.1 = gridVertex m j) :
    face (fixedFace F i j) (t ∘ fixedFaceActiveEmbedding F i j) = face F t := by
  funext a
  by_cases ha : a = i.1
  · subst a
    exact (face_fixed _ _ i.1 j (Function.update_self _ _ _)).trans ht.symm
  · have hu : fixedFace F i j a = F a := Function.update_of_ne ha _ _
    cases hf : F a with
    | inl l => rw [face_fixed F t a l hf, face_fixed _ _ a l (hu.trans hf)]
    | inr k =>
      rw [face_moving F t a k hf, face_moving _ _ a k (hu.trans hf)]
      rfl

/-- Every boundary point of a face belongs to a genuinely lower-dimensional
face. The two possible endpoint fixes use the actual neighboring grid vertices. -/
theorem face_boundary_lower {n m : ℕ} (F : FaceIndex n m)
    (t : Active F → unitInterval) (ht : t ∈ _root_.Cube.boundary (Active F)) :
    ∃ G : FaceIndex n m, faceDimension G < faceDimension F ∧ face F t ∈ faceSet G := by
  obtain ⟨i,hi⟩ := ht
  obtain ⟨k,hk⟩ := i.2
  rcases hi with hi | hi
  · let j : Fin (m+2) := k.castSucc
    have he : face F t i.1 = gridVertex m j := by
      rw [face_moving F t i.1 k hk]
      change intervalCell m k (t i) = gridVertex m j
      rw [hi]
      apply Subtype.ext
      change ((k : ℝ) + 0) / (m+1) = (k : ℝ) / (m+1)
      rw [add_zero]
    exact ⟨fixedFace F i j,fixedFace_dimension_lt F i j,
      ⟨t ∘ fixedFaceActiveEmbedding F i j,face_fixedFace F i j t he⟩⟩
  · let j : Fin (m+2) := k.succ
    have he : face F t i.1 = gridVertex m j := by
      rw [face_moving F t i.1 k hk]
      change intervalCell m k (t i) = gridVertex m j
      rw [hi]
      apply Subtype.ext
      change ((k : ℝ) + 1) / (m+1) = (((k.val+1 : ℕ) : ℝ)) / (m+1)
      simp only [Nat.cast_add,Nat.cast_one]
    exact ⟨fixedFace F i j,fixedFace_dimension_lt F i j,
      ⟨t ∘ fixedFaceActiveEmbedding F i j,face_fixedFace F i j t he⟩⟩

/-- The actual whole boundary of any newly attached face lands in the
preceding finite closed skeleton. -/
theorem face_boundary_subset_skeleton {n m r : ℕ} (F : FaceIndex n m)
    (hF : faceDimension F ≤ r + 1) (t : Active F → unitInterval)
    (ht : t ∈ _root_.Cube.boundary (Active F)) : face F t ∈ skeleton n m r := by
  obtain ⟨G,hG,hx⟩ := face_boundary_lower F t ht
  exact Set.mem_iUnion.mpr ⟨⟨G,by omega⟩,hx⟩

end Topology.CubicalSubdivision
