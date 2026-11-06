/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.CubicalSubdivision.FaceIntersections

/-! # Actual finite-stage pasting through the closed grid face skeleton

The lower skeleton together with the finitely many new compact faces is a
quotient presentation of the next skeleton. The exact intersection and
boundary identities give genuine continuous extension of compatible data.


Implementation provenance:
`Quillen/Topology/CubicalSubdivision/StagePasting.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
open scoped Topology unitInterval
namespace Topology.CubicalSubdivision
universe u

/-- Faces strictly below the attaching dimension, including the empty
initial skeleton in dimension zero. -/
def skeletonBelow (n m r : ℕ) : Set (Cube n) :=
  ⋃ F : {F : FaceIndex n m // faceDimension F < r},faceSet F.1

theorem skeletonBelow_isClosed (n m r : ℕ) : IsClosed (skeletonBelow n m r) :=
  isClosed_iUnion_of_finite (fun F ↦ faceSet_isClosed F.1)

theorem skeletonBelow_isCompact (n m r : ℕ) : IsCompact (skeletonBelow n m r) :=
  (skeletonBelow_isClosed n m r).isCompact

theorem skeletonBelow_zero (n m : ℕ) : skeletonBelow n m 0 = ∅ := by
  ext x
  simp only [skeletonBelow,Set.mem_iUnion,Set.mem_empty_iff_false,iff_false]
  rintro ⟨F,_⟩
  omega

theorem skeletonBelow_succ (n m r : ℕ) : skeletonBelow n m (r+1) = skeleton n m r := by
  ext x
  constructor
  · intro hx
    obtain ⟨F,hx⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨⟨F.1,Nat.lt_succ_iff.mp F.2⟩,hx⟩
  · intro hx
    obtain ⟨F,hx⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨⟨F.1,Nat.lt_succ_iff.mpr F.2⟩,hx⟩

theorem skeletonBelow_subset (n m r : ℕ) : skeletonBelow n m r ⊆ skeleton n m r := by
  intro x hx
  obtain ⟨F,hx⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨⟨F.1,F.2.le⟩,hx⟩

/-- The grid faces of dimension exactly `r` in the `n`-dimensional grid with `m + 1` intervals
per coordinate. -/
abbrev StageFace (n m r : ℕ) := {F : FaceIndex n m // faceDimension F = r}

theorem face_boundary_below {n m r : ℕ} (F : StageFace n m r)
    (t : Active F.1 → unitInterval) (ht : t ∈ _root_.Cube.boundary (Active F.1)) :
    face F.1 t ∈ skeletonBelow n m r := by
  obtain ⟨G,hd,hx⟩ := face_boundary_lower F.1 t ht
  exact Set.mem_iUnion.mpr ⟨⟨G,hd.trans_eq F.2⟩,hx⟩

theorem face_preimage_below {n m r : ℕ} (F : StageFace n m r) :
    (face F.1) ⁻¹' skeletonBelow n m r = _root_.Cube.boundary (Active F.1) := by
  ext t
  constructor
  · intro hx
    obtain ⟨G,⟨s,hs⟩⟩ := Set.mem_iUnion.mp hx
    have hn : F.1 ≠ G.1 := by
      intro h
      have hh := G.2
      rw [← h,F.2] at hh
      omega
    exact face_intersection_boundary_of_dimension_le F.1 G.1 hn (by omega) t s hs.symm
  · exact face_boundary_below F t

/-- The continuous face parametrization on its cube boundary, with codomain the skeleton of
faces of dimension less than `r`. -/
def stageBoundary {n m r : ℕ} (F : StageFace n m r) :
    C({t : Active F.1 → unitInterval // t ∈ _root_.Cube.boundary (Active F.1)},
      skeletonBelow n m r) where
  toFun t := ⟨face F.1 t,face_boundary_below F t t.2⟩
  continuous_toFun := by fun_prop

/-- The disjoint union of the lower skeleton and the parameter cubes of all faces of dimension
`r`. -/
abbrev StageSource (n m r : ℕ) :=
  (skeletonBelow n m r) ⊕ Σ F : StageFace n m r,Active F.1 → unitInterval

/-- The map from the lower skeleton and the new face parameter cubes onto the skeleton of
dimension at most `r`. -/
def stageProjection (n m r : ℕ) : C(StageSource n m r,skeleton n m r) where
  toFun := Sum.elim
    (fun a ↦ ⟨a.1,skeletonBelow_subset n m r a.2⟩)
    (fun z ↦ ⟨face z.1.1 z.2,Set.mem_iUnion.mpr ⟨⟨z.1.1,z.1.2.le⟩,⟨z.2,rfl⟩⟩⟩)
  continuous_toFun := by
    apply Continuous.sumElim
    · fun_prop
    · apply continuous_sigma
      intro F
      exact (face F.1).continuous.subtype_mk _

theorem stageProjection_surjective (n m r : ℕ) : Function.Surjective (stageProjection n m r) := by
  intro x
  obtain ⟨F,⟨t,ht⟩⟩ := Set.mem_iUnion.mp x.2
  by_cases hF : faceDimension F.1 < r
  · refine ⟨Sum.inl ⟨x.1,Set.mem_iUnion.mpr ⟨⟨F.1,hF⟩,⟨t,ht⟩⟩⟩,?_⟩
    rfl
  · refine ⟨Sum.inr ⟨⟨F.1,by omega⟩,t⟩,?_⟩
    exact Subtype.ext ht

theorem stageProjection_isQuotientMap (n m r : ℕ) :
    Topology.IsQuotientMap (stageProjection n m r) := by
  let : CompactSpace (skeletonBelow n m r) := isCompact_iff_compactSpace.mp
    (skeletonBelow_isCompact n m r)
  exact Topology.IsQuotientMap.of_surjective_continuous (stageProjection_surjective n m r)
    (stageProjection n m r).continuous

/-- Actual finite-stage extension from the preceding closed skeleton and
the original cell maps, with their whole-boundary agreement retained. -/
theorem exists_stage_paste (n m r : ℕ) {X : Type u} [TopologicalSpace X]
    (a : C(skeletonBelow n m r, X))
    (f : ∀ F : StageFace n m r,C((Active F.1 → unitInterval),X))
    (hf : ∀ F (t : {t : Active F.1 → unitInterval // t ∈ _root_.Cube.boundary (Active F.1)}),
      f F t = a (stageBoundary F t)) :
    ∃ g : C(skeleton n m r,X),
      (∀ x : skeletonBelow n m r,g ⟨x.1,skeletonBelow_subset n m r x.2⟩ = a x) ∧
      ∀ (F : StageFace n m r) (t : Active F.1 → unitInterval),g ⟨face F.1 t,Set.mem_iUnion.mpr
        ⟨⟨F.1,F.2.le⟩,⟨t,rfl⟩⟩⟩ = f F t := by
  let b : C(StageSource n m r,X) := ⟨Sum.elim a (fun z ↦ f z.1 z.2),
    a.continuous.sumElim (continuous_sigma (fun F ↦ (f F).continuous))⟩
  have hleft (x : skeletonBelow n m r) (F : StageFace n m r) (t : Active F.1 → unitInterval)
      (h : x.1 = face F.1 t) : a x = f F t := by
    have ht : t ∈ _root_.Cube.boundary (Active F.1) := by
      rw [← face_preimage_below F]
      change face F.1 t ∈ skeletonBelow n m r
      simpa only [← h] using x.2
    exact (congrArg a (Subtype.ext h)).trans (hf F ⟨t,ht⟩).symm
  have hb : ∀ z w,stageProjection n m r z = stageProjection n m r w → b z = b w := by
    intro z w h
    have hv := congrArg Subtype.val h
    rcases z with x | ⟨F,s⟩ <;> rcases w with y | ⟨G,t⟩
    · exact congrArg a (Subtype.ext hv)
    · exact hleft x G t hv
    · exact (hleft y F s hv.symm).symm
    · by_cases hFG : F = G
      · subst G
        exact congrArg (f F) (face_injective F.1 hv)
      · have hn : F.1 ≠ G.1 := fun hh ↦ hFG (Subtype.ext hh)
        obtain ⟨hs,ht⟩ := face_intersection_boundaries F.1 G.1 hn (F.2.trans G.2.symm) s t hv
        exact (hf F ⟨s,hs⟩).trans ((congrArg a (Subtype.ext hv)).trans (hf G ⟨t,ht⟩).symm)
  choose rep hrep using stageProjection_surjective n m r
  let g : skeleton n m r → X := fun x ↦ b (rep x)
  have hg (z : StageSource n m r) : g (stageProjection n m r z) = b z :=
    hb (rep _) z (hrep _)
  have hc : Continuous g := by
    apply (stageProjection_isQuotientMap n m r).continuous_iff.2
    have he : g ∘ stageProjection n m r = b := funext hg
    rw [he]
    exact b.continuous
  exact ⟨⟨g,hc⟩,fun x ↦ hg (Sum.inl x),fun F t ↦ hg (Sum.inr ⟨F,t⟩)⟩

end Topology.CubicalSubdivision
