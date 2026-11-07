/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.Cube.ThinSupportEmbedding
public import Colib.Topology.CubicalSubdivision.FaceBoundaryTopology
public import Colib.Topology.CubicalSubdivision.StagePasting
public import Colib.Topology.CubicalSubdivision.FaceContainment

/-!
# Actual lower-face compatibility of thin supports

The intrinsic parameter coordinates of each original grid face are reindexed by their actual
finite cardinality. Retaining a subset of those coordinates preserves the same band count.
Explicit boundary faces carry their original point and coordinate embedding, so a lower-face
support estimate can be used at the exact boundary point being attached.
-/

/-! Implementation provenance: adapted from
`Quillen/Topology/CubicalSubdivision/FaceThinSupport.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, finite bounds,
whole path families and universe parameters are retained in their native owners. -/
@[expose] public section

noncomputable section
open Topology TopCat

open scoped Topology unitInterval

namespace Topology.CubicalSubdivision

/-- The support region measured in the original active coordinates of a grid face. -/
def faceThinSupport {n m : ℕ} (F : FaceIndex n m) (a b : unitInterval) (p : ℕ) :
    Set (Active F → unitInterval) :=
  {t | (t ∘ (activeEquivFin F).symm) ∈ _root_.Cube.thinSupport a b p}

/-- A face cannot have more coordinates in a band than its actual dimension, including
zero-dimensional faces and positive support counts. -/
theorem not_mem_faceThinSupport_of_dimension_lt {n m : ℕ} (F : FaceIndex n m)
    (a b : unitInterval) (p : ℕ) (hp : faceDimension F < p)
    (t : Active F → unitInterval) : t ∉ faceThinSupport F a b p := by
  intro ht
  change p ≤ (_root_.Cube.bandCoordinates a b (t ∘ (activeEquivFin F).symm)).card at ht
  have hc := Finset.card_le_card
    (Finset.subset_univ (_root_.Cube.bandCoordinates a b (t ∘ (activeEquivFin F).symm)))
  rw [Finset.card_univ, Fintype.card_fin] at hc
  exact Nat.not_lt_of_ge (ht.trans hc) hp

/-- Retaining an actual subfamily of moving coordinates preserves the same support count. -/
theorem faceThinSupport_of_embedding {n m : ℕ} (F G : FaceIndex n m)
    (e : Active G ↪ Active F) (a b : unitInterval) (p : ℕ)
    (t : Active F → unitInterval) (ht : t ∘ e ∈ faceThinSupport G a b p) :
    t ∈ faceThinSupport F a b p := by
  let e' := (activeEquivFin G).symm.toEmbedding.trans
    (e.trans (activeEquivFin F).toEmbedding)
  apply _root_.Cube.thinSupport_of_coordinateEmbedding a b e'
    (t ∘ (activeEquivFin F).symm) p
  convert ht using 1
  simp only [e', Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
    Function.comp_def, Equiv.symm_apply_apply, faceThinSupport, Set.mem_ofPred_eq]

/-- Fixing a single coordinate leaves an actual subface whenever its chosen grid vertex
already belongs to the original face. The same original affine coordinates are used. -/
theorem fixedFace_subset_of_vertex {n m : ℕ} (F : FaceIndex n m) (i : Active F)
    (j : Fin (m + 2)) (t : Active F → unitInterval)
    (ht : face F t i.val = gridVertex m j) : faceSet (fixedFace F i j) ⊆ faceSet F := by
  classical
  rintro x ⟨v, rfl⟩
  let u : Active F → unitInterval := fun a ↦ if h : a.val = i.val then t i else
    v ⟨a.val, by
      obtain ⟨k, hk⟩ := a.property
      exact ⟨k, (Function.update_of_ne h _ _).trans hk⟩⟩
  refine ⟨u, ?_⟩
  funext k
  by_cases hki : k = i.val
  · subst k
    obtain ⟨l, hl⟩ := i.property
    rw [face_moving F u i.val l hl,
      face_fixed (fixedFace F i j) v i.val j (Function.update_self _ _ _)]
    have hu : u ⟨i.val, l, hl⟩ = t i := by simp only [u, dite_eq_left rfl]
    rw [hu]
    exact (face_moving F t i.val l hl).symm.trans ht
  · have he : fixedFace F i j k = F k := Function.update_of_ne hki _ _
    cases hk : F k with
    | inl l => rw [face_fixed F u k l hk, face_fixed _ _ k l (he.trans hk)]
    | inr l =>
      rw [face_moving F u k l hk, face_moving _ _ k l (he.trans hk)]
      congr 1
      simp only [u, dite_eq_right hki]

/-- Each actual boundary point admits a strictly lower incident face, retaining the point,
its parameter restriction, and every band-support implication. -/
theorem face_boundary_lower_with_support {n m : ℕ} (F : FaceIndex n m)
    (t : Active F → unitInterval) (ht : t ∈ _root_.Cube.boundary (Active F)) :
    ∃ G : FaceIndex n m, ∃ u : Active G → unitInterval,
      faceDimension G < faceDimension F ∧ faceSet G ⊆ faceSet F ∧ face G u = face F t ∧
        ∀ (a b : unitInterval) (p : ℕ), u ∈ faceThinSupport G a b p →
          t ∈ faceThinSupport F a b p := by
  obtain ⟨i, hi⟩ := ht
  obtain ⟨k, hk⟩ := i.property
  have hfix (j : Fin (m + 2)) (he : face F t i.val = gridVertex m j) :
      ∃ G : FaceIndex n m, ∃ u : Active G → unitInterval,
        faceDimension G < faceDimension F ∧ faceSet G ⊆ faceSet F ∧ face G u = face F t ∧
          ∀ (a b : unitInterval) (p : ℕ), u ∈ faceThinSupport G a b p →
            t ∈ faceThinSupport F a b p := by
    refine ⟨fixedFace F i j, t ∘ fixedFaceActiveEmbedding F i j,
      fixedFace_dimension_lt F i j, fixedFace_subset_of_vertex F i j t he,
      face_fixedFace F i j t he, ?_⟩
    intro a b p hu
    exact faceThinSupport_of_embedding F (fixedFace F i j)
      (fixedFaceActiveEmbedding F i j) a b p t hu
  rcases hi with hi | hi
  · apply hfix k.castSucc
    rw [face_moving F t i.val k hk]
    change intervalCell m k (t i) = gridVertex m k.castSucc
    rw [hi]
    apply Subtype.ext
    change ((k : ℝ) + 0) / (m + 1) = (k : ℝ) / (m + 1)
    rw [add_zero]
  · apply hfix k.succ
    rw [face_moving F t i.val k hk]
    change intervalCell m k (t i) = gridVertex m k.succ
    rw [hi]
    apply Subtype.ext
    change ((k : ℝ) + 1) / (m + 1) = (((k.val + 1 : ℕ) : ℝ)) / (m + 1)
    simp only [Nat.cast_add, Nat.cast_one]

/-- Whole-face containment retains the label of every originally moving coordinate. -/
theorem moving_label_of_subset {n m : ℕ} (F G : FaceIndex n m)
    (hFG : faceSet F ⊆ faceSet G) (i : Fin n) (k : Fin (m + 1))
    (hF : F i = Sum.inr k) : G i = Sum.inr k := by
  let half : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
  let s : Active F → unitInterval := fun _ ↦ half
  obtain ⟨t, ht⟩ := hFG ⟨s, rfl⟩
  have hs : s ∉ _root_.Cube.boundary (Active F) := by
    rintro ⟨j, hj | hj⟩ <;>
      have h := congrArg (fun x : unitInterval ↦ (x : ℝ)) hj <;> norm_num [s, half] at h
  cases hG : G i with
  | inl j =>
    have he := congrFun ht i
    rw [face_fixed G t i j hG, face_moving F s i k hF] at he
    exact (hs ⟨⟨i, k, hF⟩, intervalCell_eq_gridVertex_boundary m k j _ he.symm⟩).elim
  | inr l =>
    have hkl := moving_label_eq_of_interior F G s t hs ht.symm i k l hF hG
    rw [hkl]

/-- The actual moving-coordinate embedding associated to whole-face containment. -/
def activeEmbeddingOfSubset {n m : ℕ} (F G : FaceIndex n m)
    (hFG : faceSet F ⊆ faceSet G) : Active F ↪ Active G where
  toFun i := ⟨i.val, by
    obtain ⟨k, hk⟩ := i.property
    exact ⟨k, moving_label_of_subset F G hFG i.val k hk⟩⟩
  inj' i j h := Subtype.ext (congrArg (fun z : Active G ↦ z.val) h)

/-- A point common to incident faces retains all parameter coordinates of the smaller face. -/
theorem parameters_restrict_of_subset {n m : ℕ} (F G : FaceIndex n m)
    (hFG : faceSet F ⊆ faceSet G) (s : Active F → unitInterval)
    (t : Active G → unitInterval) (h : face F s = face G t) :
    t ∘ activeEmbeddingOfSubset F G hFG = s := by
  funext i
  obtain ⟨k, hk⟩ := i.property
  have hG := moving_label_of_subset F G hFG i.val k hk
  have he := congrFun h i.val
  rw [face_moving F s i.val k hk, face_moving G t i.val k hG] at he
  exact (intervalCell_injective m k he).symm

/-- Endpoint support in a normalized face supplies the same support bound in every incident
containing face, using the identical original point and its literal coordinates. -/
theorem faceThinSupport_of_subset {n m : ℕ} (F G : FaceIndex n m)
    (hFG : faceSet F ⊆ faceSet G) (s : Active F → unitInterval)
    (t : Active G → unitInterval) (h : face F s = face G t)
    (a b : unitInterval) (p : ℕ) (hs : s ∈ faceThinSupport F a b p) :
    t ∈ faceThinSupport G a b p := by
  apply faceThinSupport_of_embedding G F (activeEmbeddingOfSubset F G hFG) a b p t
  rw [parameters_restrict_of_subset F G hFG s t h]
  exact hs

/-- Support bounds on all lower incident faces give the precise boundary support hypothesis
for the next original face; no chart is chosen or discarded. -/
theorem boundary_faceThinSupport_of_lower {n m r : ℕ} (F : StageFace n m r)
    {Y : Type*} [TopologicalSpace Y] (v : C(skeletonBelow n m r, Y))
    (A : Set Y) (a b : unitInterval) (p : ℕ)
    (hv : ∀ (G : FaceIndex n m) (hG : faceDimension G < r),
      faceSet G ⊆ faceSet F.val → ∀ u : Active G → unitInterval,
        v ⟨face G u, Set.mem_iUnion.mpr ⟨⟨G, hG⟩, ⟨u, rfl⟩⟩⟩ ∈ A →
          u ∈ faceThinSupport G a b p)
    (z : {t : Active F.val → unitInterval // t ∈ _root_.Cube.boundary (Active F.val)})
    (hz : v (stageBoundary F z) ∈ A) : z.val ∈ faceThinSupport F.val a b p := by
  obtain ⟨G, u, hdim, hGF, hpoint, hsupport⟩ :=
    face_boundary_lower_with_support F.val z.val z.property
  apply hsupport a b p
  apply hv G (hdim.trans_eq F.property) hGF u
  have he : (⟨face G u, Set.mem_iUnion.mpr
      ⟨⟨G, hdim.trans_eq F.property⟩, ⟨u, rfl⟩⟩⟩ : skeletonBelow n m r) = stageBoundary F z :=
    Subtype.ext hpoint
  rw [he]
  exact hz

end Topology.CubicalSubdivision
