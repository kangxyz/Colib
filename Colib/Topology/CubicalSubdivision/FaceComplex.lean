/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.CubicalSubdivision.Faces

/-! # The actual finite face skeleton of an affine cubical grid

A coordinate is either a grid vertex or a moving grid interval. These labels
are canonical, so shared faces are represented once. The resulting finite
closed skeleton is a concrete geometric object, prior to any lifting claim.


Implementation provenance:
`Quillen/Topology/CubicalSubdivision/FaceComplex.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
open scoped Topology unitInterval
namespace Topology.CubicalSubdivision

/-- A coordinate label in the grid: one of the `m + 2` vertices or one of the `m + 1` moving
intervals. -/
abbrev FaceLabel (m : ℕ) := Fin (m+2) ⊕ Fin (m+1)
/-- A choice of vertex or moving-interval label in each of the `n` cube coordinates. -/
abbrev FaceIndex (n m : ℕ) := Fin n → FaceLabel m
/-- The coordinates of a face labelled by moving intervals, rather than fixed grid vertices. -/
abbrev Active {n m : ℕ} (F : FaceIndex n m) := {i : Fin n // ∃ k, F i = Sum.inr k}

/-- An actual grid vertex, including both outer endpoints. -/
def gridVertex (m : ℕ) (j : Fin (m + 2)) : unitInterval := ⟨(j : ℝ)/(m + 1), by
  have hd : (0 : ℝ) < m+1 := by positivity
  constructor
  · exact div_nonneg (by positivity) hd.le
  · apply (div_le_one hd).2
    exact_mod_cast Nat.le_of_lt_succ j.isLt⟩

theorem exists_fixed_of_not_active {n m : ℕ} (F : FaceIndex n m) (i : Fin n)
    (h : ¬ ∃ k, F i = Sum.inr k) : ∃ j, F i = Sum.inl j := by
  cases hi : F i with
  | inl j => exact ⟨j,rfl⟩
  | inr k => exact (h ⟨k,hi⟩).elim

/-- One literal coordinate map, expressed without a dependent case split on
its continuously varying parameter. -/
def faceCoordinate {n m : ℕ} (F : FaceIndex n m) (i : Fin n) :
    C((Active F → unitInterval),unitInterval) := by
  classical
  exact if h : ∃ k, F i = Sum.inr k then
    (intervalCell m h.choose).comp ⟨fun t ↦ t ⟨i,h⟩,continuous_apply _⟩
  else ContinuousMap.const _ (gridVertex m (exists_fixed_of_not_active F i h).choose)

/-- The original product-coordinate map of a canonically labeled face. -/
def face {n m : ℕ} (F : FaceIndex n m) : C((Active F → unitInterval), Cube n) where
  toFun t i := faceCoordinate F i t
  continuous_toFun := continuous_pi (fun i ↦ (faceCoordinate F i).continuous)

@[simp] theorem face_fixed {n m : ℕ} (F : FaceIndex n m) (t : Active F → unitInterval)
    (i : Fin n) (j : Fin (m + 2)) (h : F i = Sum.inl j) : face F t i = gridVertex m j := by
  have hn : ¬ ∃ k, F i = Sum.inr k := by
    rintro ⟨k,hk⟩
    cases h.symm.trans hk
  have hj : (exists_fixed_of_not_active F i hn).choose = j :=
    Sum.inl.inj ((exists_fixed_of_not_active F i hn).choose_spec.symm.trans h)
  simp only [face,ContinuousMap.coe_mk,faceCoordinate,dite_eq_right hn,ContinuousMap.const_apply,hj]

@[simp] theorem face_moving {n m : ℕ} (F : FaceIndex n m) (t : Active F → unitInterval)
    (i : Fin n) (k : Fin (m + 1)) (h : F i = Sum.inr k) :
    face F t i = intervalCell m k (t ⟨i,k,h⟩) := by
  have ha : ∃ k, F i = Sum.inr k := ⟨k,h⟩
  have hk : ha.choose = k := Sum.inr.inj (ha.choose_spec.symm.trans h)
  simp only [face,ContinuousMap.coe_mk,faceCoordinate,dite_eq_left ha,ContinuousMap.comp_apply,hk]

theorem face_injective {n m : ℕ} (F : FaceIndex n m) : Function.Injective (face F) := by
  intro s t h
  funext i
  obtain ⟨k,hk⟩ := i.2
  have hi := congrFun h i.1
  rw [face_moving F s i.1 k hk, face_moving F t i.1 k hk] at hi
  exact intervalCell_injective m k hi

theorem face_isClosedEmbedding {n m : ℕ} (F : FaceIndex n m) :
    Topology.IsClosedEmbedding (face F) :=
  (face F).continuous.isClosedEmbedding (face_injective F)

/-- The number of moving-interval coordinates in the face label `F`. -/
def faceDimension {n m : ℕ} (F : FaceIndex n m) : ℕ := Fintype.card (Active F)

theorem faceDimension_le {n m : ℕ} (F : FaceIndex n m) : faceDimension F ≤ n := by
  simpa only [faceDimension, Fintype.card_fin] using
    Fintype.card_le_of_injective (fun i : Active F ↦ i.1) Subtype.val_injective

/-- The geometric face of the unit cube given by the range of the parametrization `face F`. -/
def faceSet {n m : ℕ} (F : FaceIndex n m) : Set (Cube n) := Set.range (face F)

theorem faceSet_isCompact {n m : ℕ} (F : FaceIndex n m) : IsCompact (faceSet F) :=
  isCompact_range (face F).continuous

theorem faceSet_isClosed {n m : ℕ} (F : FaceIndex n m) : IsClosed (faceSet F) :=
  (faceSet_isCompact F).isClosed

/-- The actual finite union of all faces of dimension at most r. -/
def skeleton (n m r : ℕ) : Set (Cube n) :=
  ⋃ F : {F : FaceIndex n m // faceDimension F ≤ r}, faceSet F.val

theorem skeleton_isClosed (n m r : ℕ) : IsClosed (skeleton n m r) :=
  isClosed_iUnion_of_finite (fun F ↦ faceSet_isClosed F.val)

theorem skeleton_isCompact (n m r : ℕ) : IsCompact (skeleton n m r) :=
  (skeleton_isClosed n m r).isCompact

theorem skeleton_mono (n m : ℕ) {r s : ℕ} (h : r ≤ s) :
    skeleton n m r ⊆ skeleton n m s := by
  intro x hx
  obtain ⟨F,hx⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨⟨F.1,F.2.trans h⟩,hx⟩

/-- A full-dimensional affine cell has exactly its all-moving face labels. -/
def maximalFace {n m : ℕ} (k : CellIndex n m) : FaceIndex n m := fun i ↦ Sum.inr (k i)

@[simp] theorem maximalFace_apply {n m : ℕ} (k : CellIndex n m) (t : Cube n) :
    face (maximalFace k) (fun i ↦ t i.1) = cell n m k t := by
  funext i
  exact face_moving _ _ i (k i) rfl

/-- The final actual face skeleton is the whole original cube. -/
theorem skeleton_top (n m : ℕ) : skeleton n m n = Set.univ := by
  ext x
  simp only [Set.mem_univ, iff_true]
  obtain ⟨k,t,ht⟩ := cell_covers n m x
  refine Set.mem_iUnion.mpr ⟨⟨maximalFace k,faceDimension_le _⟩,?_⟩
  exact ⟨fun i ↦ t i.1, (maximalFace_apply k t).trans ht⟩

end Topology.CubicalSubdivision
