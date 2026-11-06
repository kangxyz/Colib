/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.CubicalSubdivision.FaceIntersections

/-! # Interior intersections determine actual grid-face containment

A canonical cubical face which meets another face at one of its interior
points lies wholly in that face. This controls all incident chart constraints
when filling faces in increasing dimension, including zero-dimensional faces.


Implementation provenance:
`Quillen/Topology/CubicalSubdivision/FaceContainment.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
open scoped Topology unitInterval
namespace Topology.CubicalSubdivision

/-- At an interior intersection, matching moving coordinates use the same
actual grid interval, not just intervals with a common endpoint. -/
theorem moving_label_eq_of_interior {n m : ℕ} (F G : FaceIndex n m)
    (s : Active F → unitInterval) (t : Active G → unitInterval)
    (hs : s ∉ _root_.Cube.boundary (Active F)) (he : face F s = face G t)
    (i : Fin n) (k l : Fin (m + 1)) (hf : F i = Sum.inr k) (hg : G i = Sum.inr l) : k = l := by
  have hi := congrFun he i
  rw [face_moving F s i k hf,face_moving G t i l hg] at hi
  by_contra hn
  rcases lt_or_gt_of_ne hn with hk | hk
  · obtain ⟨_,ha,_⟩ := intervalCell_eq_endpoints_of_lt m k l hk
      (s ⟨i,k,hf⟩) (t ⟨i,l,hg⟩) hi
    exact hs ⟨⟨i,k,hf⟩,Or.inr ha⟩
  · obtain ⟨_,_,ha⟩ := intervalCell_eq_endpoints_of_lt m l k hk
      (t ⟨i,l,hg⟩) (s ⟨i,k,hf⟩) hi.symm
    exact hs ⟨⟨i,k,hf⟩,Or.inl ha⟩

/-- An interior point in the second face forces containment of the entire
first face, without any dimension or maximal-face assumption. -/
theorem faceSet_subset_of_interior {n m : ℕ} (F G : FaceIndex n m)
    (s : Active F → unitInterval) (t : Active G → unitInterval)
    (hs : s ∉ _root_.Cube.boundary (Active F)) (he : face F s = face G t) :
    faceSet F ⊆ faceSet G := by
  classical
  rintro x ⟨u,rfl⟩
  have hv : ∀ a : Active G,∃ v : unitInterval,
      ∀ l (hl : G a.1 = Sum.inr l), intervalCell m l v = face F u a.1 := by
    intro a
    cases hf : F a.1 with
    | inl j =>
      refine ⟨t a,?_⟩
      intro l hl
      have hi := congrFun he a.1
      rw [face_fixed F s a.1 j hf,face_moving G t a.1 l hl] at hi
      exact hi.symm.trans (face_fixed F u a.1 j hf).symm
    | inr k =>
      refine ⟨u ⟨a.1,k,hf⟩,?_⟩
      intro l hl
      have hkl := moving_label_eq_of_interior F G s t hs he a.1 k l hf hl
      subst l
      exact (face_moving F u a.1 k hf).symm
  choose v hv using hv
  refine ⟨v,?_⟩
  funext i
  cases hg : G i with
  | inr l =>
    rw [face_moving G v i l hg]
    exact hv ⟨i,l,hg⟩ l hg
  | inl j =>
    have hi := congrFun he i
    rw [face_fixed G t i j hg] at hi
    cases hf : F i with
    | inl k =>
      rw [face_fixed F s i k hf] at hi
      rw [face_fixed G v i j hg,face_fixed F u i k hf]
      exact hi.symm
    | inr k =>
      rw [face_moving F s i k hf] at hi
      exact (hs ⟨⟨i,k,hf⟩,intervalCell_eq_gridVertex_boundary m k j (s ⟨i,k,hf⟩) hi⟩).elim

/-- A face intersection either belongs to the original full parameter
boundary or forces whole-face containment. -/
theorem face_boundary_or_subset_of_mem {n m : ℕ} (F G : FaceIndex n m)
    (s : Active F → unitInterval) (hx : face F s ∈ faceSet G) :
    s ∈ _root_.Cube.boundary (Active F) ∨ faceSet F ⊆ faceSet G := by
  by_cases hs : s ∈ _root_.Cube.boundary (Active F)
  · exact Or.inl hs
  · obtain ⟨t,ht⟩ := hx
    exact Or.inr (faceSet_subset_of_interior F G s t hs ht.symm)

end Topology.CubicalSubdivision
