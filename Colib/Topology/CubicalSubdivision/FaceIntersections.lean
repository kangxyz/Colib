/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.CubicalSubdivision.FaceBoundary

/-! # Exact boundary intersections in the finite grid face skeleton

Implementation provenance:
`Quillen/Topology/CubicalSubdivision/FaceIntersections.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
open scoped Topology unitInterval
namespace Topology.CubicalSubdivision

theorem gridVertex_injective (m : ℕ) : Function.Injective (gridVertex m) := by
  intro i j h
  have he := congrArg (fun t : unitInterval ↦ (t : ℝ)) h
  change (i : ℝ)/(m+1) = (j : ℝ)/(m+1) at he
  have hd : (m+1 : ℝ) ≠ 0 := by positivity
  have hi := (div_left_inj' hd).mp he
  apply Fin.ext
  exact_mod_cast hi

/-- A moving interval meets a grid vertex only at an actual endpoint. -/
theorem intervalCell_eq_gridVertex_boundary (m : ℕ) (k : Fin (m + 1))
    (j : Fin (m + 2)) (t : unitInterval) (h : intervalCell m k t = gridVertex m j) :
    t = 0 ∨ t = 1 := by
  have he := congrArg (fun t : unitInterval ↦ (t : ℝ)) h
  change ((k : ℝ)+t)/(m+1) = (j : ℝ)/(m+1) at he
  have hd : (m+1 : ℝ) ≠ 0 := by positivity
  have hi := (div_left_inj' hd).mp he
  by_cases hj : (j : ℕ) ≤ k
  · left
    apply Subtype.ext
    change (t : ℝ) = 0
    have hj' : (j : ℝ) ≤ k := by exact_mod_cast hj
    linarith [t.2.1]
  · right
    apply Subtype.ext
    change (t : ℝ) = 1
    have hj' : (k : ℝ)+1 ≤ j := by exact_mod_cast (by omega : (k : ℕ)+1 ≤ j)
    linarith [t.2.2]

/-- At an interior point, every moving coordinate of the first face must
also move in any second face containing that point. -/
def activeEmbeddingOfInterior {n m : ℕ} (F G : FaceIndex n m)
    (s : Active F → unitInterval) (t : Active G → unitInterval)
    (hs : s ∉ _root_.Cube.boundary (Active F)) (he : face F s = face G t) :
    Active F ↪ Active G where
  toFun i := ⟨i.1,by
    obtain ⟨k,hk⟩ := i.2
    cases hg : G i.1 with
    | inr l => exact ⟨l,rfl⟩
    | inl j =>
      have hi := congrFun he i.1
      rw [face_moving F s i.1 k hk,face_fixed G t i.1 j hg] at hi
      have hb := intervalCell_eq_gridVertex_boundary m k j (s i) hi
      exact (hs ⟨i,hb⟩).elim⟩
  inj' i j h := Subtype.ext (congrArg (fun z : Active G ↦ z.1) h)

@[simp] theorem activeEmbeddingOfInterior_val {n m : ℕ} (F G : FaceIndex n m)
    (s : Active F → unitInterval) (t : Active G → unitInterval)
    (hs : s ∉ _root_.Cube.boundary (Active F)) (he : face F s = face G t)
    (i : Active F) : (activeEmbeddingOfInterior F G s t hs he i).1 = i.1 := rfl

/-- An interior point determines its face among faces of no larger dimension. -/
theorem face_eq_of_interior_of_dimension_le {n m : ℕ} (F G : FaceIndex n m)
    (s : Active F → unitInterval) (t : Active G → unitInterval)
    (hs : s ∉ _root_.Cube.boundary (Active F)) (he : face F s = face G t)
    (hdim : faceDimension G ≤ faceDimension F) : F = G := by
  let e := activeEmbeddingOfInterior F G s t hs he
  have hes : Function.Surjective e := by
    by_contra hn
    have hlt := Fintype.card_lt_of_injective_not_surjective e e.injective hn
    change Fintype.card (Active G) ≤ Fintype.card (Active F) at hdim
    omega
  funext i
  cases hf : F i with
  | inl j =>
    cases hg : G i with
    | inl k =>
      have hi := congrFun he i
      rw [face_fixed F s i j hf,face_fixed G t i k hg] at hi
      rw [gridVertex_injective m hi]
    | inr l =>
      obtain ⟨a,ha⟩ := hes ⟨i,l,hg⟩
      have hv : a.1 = i := congrArg (fun z : Active G ↦ z.1) ha
      obtain ⟨k,hk⟩ := a.2
      rw [hv,hf] at hk
      cases hk
  | inr k =>
    let a : Active F := ⟨i,k,hf⟩
    obtain ⟨l,hg⟩ := (e a).2
    change G i = Sum.inr l at hg
    have hi := congrFun he i
    rw [face_moving F s i k hf,face_moving G t i l hg] at hi
    by_cases hkl : k = l
    · exact (congrArg Sum.inr hkl).trans hg.symm
    · rcases lt_or_gt_of_ne hkl with h | h
      · obtain ⟨_,ha,_⟩ := intervalCell_eq_endpoints_of_lt m k l h (s a)
          (t ⟨i,l,hg⟩) hi
        exact (hs ⟨a,Or.inr ha⟩).elim
      · obtain ⟨_,_,ha⟩ := intervalCell_eq_endpoints_of_lt m l k h (t ⟨i,l,hg⟩)
          (s a) hi.symm
        exact (hs ⟨a,Or.inl ha⟩).elim

/-- Any intersection with a different face of no larger dimension lies on
the whole original boundary of the first face. -/
theorem face_intersection_boundary_of_dimension_le {n m : ℕ} (F G : FaceIndex n m)
    (hFG : F ≠ G) (hdim : faceDimension G ≤ faceDimension F)
    (s : Active F → unitInterval) (t : Active G → unitInterval)
    (he : face F s = face G t) : s ∈ _root_.Cube.boundary (Active F) := by
  by_contra hs
  exact hFG (face_eq_of_interior_of_dimension_le F G s t hs he hdim)

/-- Distinct equal-dimensional faces meet only on both full boundaries. -/
theorem face_intersection_boundaries {n m : ℕ} (F G : FaceIndex n m)
    (hFG : F ≠ G) (hdim : faceDimension F = faceDimension G)
    (s : Active F → unitInterval) (t : Active G → unitInterval)
    (he : face F s = face G t) :
    s ∈ _root_.Cube.boundary (Active F) ∧ t ∈ _root_.Cube.boundary (Active G) :=
  ⟨face_intersection_boundary_of_dimension_le F G hFG hdim.ge s t he,
    face_intersection_boundary_of_dimension_le G F (Ne.symm hFG) hdim.le t s he.symm⟩

/-- The preimage of the preceding skeleton is exactly the whole boundary.
This is the actual attaching-subspace identity needed for cellwise lifting. -/
theorem face_preimage_skeleton {n m r : ℕ} (F : FaceIndex n m)
    (hF : faceDimension F = r + 1) :
    (face F) ⁻¹' skeleton n m r = _root_.Cube.boundary (Active F) := by
  ext s
  constructor
  · intro hs
    obtain ⟨G,⟨t,ht⟩⟩ := Set.mem_iUnion.mp hs
    have hne : F ≠ G.1 := by
      intro h
      have hd := G.2
      rw [← h,hF] at hd
      omega
    exact face_intersection_boundary_of_dimension_le F G.1 hne (by omega) s t ht.symm
  · exact face_boundary_subset_skeleton F hF.le s

end Topology.CubicalSubdivision
