/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.CubicalSubdivision.TwoChartFaceNormalization
public import Colib.Topology.CubicalSubdivision.StageHomotopyPasting

/-!
# Incident-face-compatible normalization over the actual finite grid

The skeleton invariant records the original homotopy and every incident chart constraint,
including containing faces which have not yet been attached. Face-coordinate embeddings
transport endpoint support to those larger faces. Whole paths are pasted through the original
stage quotient, keeping all lower-skeleton times identical.
-/

/-! Implementation provenance: adapted from
`Quillen/Topology/CubicalSubdivision/TwoChartGridNormalization.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, finite bounds,
whole path families and universe parameters are retained in their native owners. -/
@[expose] public section

noncomputable section
open Topology TopCat

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open scoped Topology unitInterval

universe u

namespace Topology.CubicalSubdivision

variable {Y : Type u} [TopologicalSpace Y]

/-- A homotopy on the actual lower skeleton, controlled on every incident original chart. -/
structure TwoChartStageHomotopy (n mesh r : ℕ) (b : C(Cube n, Y)) (U V : Set Y)
    (a₁ b₁ a₂ b₂ : unitInterval) (p q : ℕ) where
  /-- The actual endpoint map on the lower skeleton. -/
  endpoint : C(skeletonBelow n mesh r, Y)
  /-- The original map deforms to this endpoint on the unchanged lower skeleton. -/
  homotopy : (b.comp ⟨Subtype.val, continuous_subtype_val⟩).Homotopy endpoint
  /-- Every original left-chart face constraint is retained at all times. -/
  left_mem : ∀ (G : FaceIndex n mesh), (∀ s, b (face G s) ∈ U) →
    ∀ t x, x.val ∈ faceSet G → homotopy (t, x) ∈ U
  /-- Every original right-chart face constraint is retained at all times. -/
  right_mem : ∀ (G : FaceIndex n mesh), (∀ s, b (face G s) ∈ V) →
    ∀ t x, x.val ∈ faceSet G → homotopy (t, x) ∈ V
  /-- Every face originally mapped into the overlap remains pointwise fixed. -/
  overlap_fixed : ∀ (G : FaceIndex n mesh), (∀ s, b (face G s) ∈ U ∩ V) →
    ∀ t x, x.val ∈ faceSet G → homotopy (t, x) = b x.val
  /-- The left endpoint support is controlled in all incident containing coordinates. -/
  left_support : ∀ (G : FaceIndex n mesh), (∀ s, b (face G s) ∈ U) →
    ∀ x (s : Active G → unitInterval), face G s = x.val →
      endpoint x ∉ V → s ∈ faceThinSupport G a₁ b₁ (p + 1)
  /-- The right endpoint support has the same all-incident invariant. -/
  right_support : ∀ (G : FaceIndex n mesh), (∀ s, b (face G s) ∈ V) →
    ∀ x (s : Active G → unitInterval), face G s = x.val →
      endpoint x ∉ U → s ∈ faceThinSupport G a₂ b₂ (q + 1)

namespace TwoChartStageHomotopy

/-- The initial skeleton is genuinely empty, so all original constraints hold there. -/
def empty (n mesh : ℕ) (b : C(Cube n, Y)) (U V : Set Y)
    (a₁ b₁ a₂ b₂ : unitInterval) (p q : ℕ) :
    TwoChartStageHomotopy n mesh 0 b U V a₁ b₁ a₂ b₂ p q := by
  let : IsEmpty (skeletonBelow n mesh 0) := ⟨fun x ↦ by
    have hx := x.property
    simp only [skeletonBelow_zero, Set.mem_empty_iff_false] at hx⟩
  let v := b.comp (⟨Subtype.val, continuous_subtype_val⟩ : C(skeletonBelow n mesh 0, Cube n))
  exact {
    endpoint := v
    homotopy := ContinuousMap.Homotopy.refl v
    left_mem := fun _ _ _ x _ ↦ isEmptyElim x
    right_mem := fun _ _ _ x _ ↦ isEmptyElim x
    overlap_fixed := fun _ _ _ x _ ↦ isEmptyElim x
    left_support := fun _ _ x _ _ _ ↦ isEmptyElim x
    right_support := fun _ _ x _ _ _ ↦ isEmptyElim x }

/-- Attach every face of the next dimension while retaining all incident chart constraints.
The whole homotopy on the preceding skeleton is unchanged at every original point and time. -/
theorem exists_succ {n mesh r : ℕ} {b : C(Cube n, Y)} {U V : Set Y}
    {a₁ b₁ a₂ b₂ : unitInterval} {p q : ℕ}
    (D : TwoChartStageHomotopy n mesh r b U V a₁ b₁ a₂ b₂ p q)
    (hab : a₁ < b₁) (hce : a₂ < b₂)
    (hUV : IsHomotopyConnectedMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C({y : U // y.val ∈ V}, U)) p)
    (hVU : IsHomotopyConnectedMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C({y : V // y.val ∈ U}, V)) q)
    (hcover : ∀ G : FaceIndex n mesh,
      (∀ s, b (face G s) ∈ U) ∨ ∀ s, b (face G s) ∈ V) :
    ∃ D' : TwoChartStageHomotopy n mesh (r + 1) b U V a₁ b₁ a₂ b₂ p q,
      ∀ t (x : skeletonBelow n mesh r) (y : skeletonBelow n mesh (r + 1)),
        x.val = y.val → D'.homotopy (t, y) = D.homotopy (t, x) := by
  classical
  let H (F : StageFace n mesh r) : C(unitInterval ×
      {s : Active F.val → unitInterval // s ∈ _root_.Cube.boundary (Active F.val)}, Y) :=
    ⟨fun z ↦ D.homotopy (z.1, stageBoundary F z.2), by fun_prop⟩
  have hlocal (F : StageFace n mesh r) := exists_face_two_chart_normalization F.val U V
    a₁ b₁ a₂ b₂ hab hce p q hUV hVU (b.comp (face F.val)) (hcover F.val) (H F)
    (fun z ↦ D.homotopy.map_zero_left (stageBoundary F z))
    (fun h t z ↦ D.left_mem F.val h t (stageBoundary F z) ⟨z.val, rfl⟩)
    (fun h t z ↦ D.right_mem F.val h t (stageBoundary F z) ⟨z.val, rfl⟩)
    (fun h t z ↦ D.overlap_fixed F.val h t (stageBoundary F z) ⟨z.val, rfl⟩)
    (fun h z hz ↦ D.left_support F.val h (stageBoundary F z) z.val rfl
      (by
        intro he
        apply hz
        change D.homotopy (1, stageBoundary F z) ∈ _
        exact (congrArg (fun y ↦ y ∈ V)
          (D.homotopy.map_one_left (stageBoundary F z))).mpr he))
    (fun h z hz ↦ D.right_support F.val h (stageBoundary F z) z.val rfl
      (by
        intro he
        apply hz
        change D.homotopy (1, stageBoundary F z) ∈ _
        exact (congrArg (fun y ↦ y ∈ U)
          (D.homotopy.map_one_left (stageBoundary F z))).mpr he))
  choose c K htrack hU hV hfix hSU hSV using hlocal
  have hc (F : StageFace n mesh r)
      (z : {s : Active F.val → unitInterval // s ∈ _root_.Cube.boundary (Active F.val)}) :
      c F z.val = D.endpoint (stageBoundary F z) :=
    ((K F).map_one_left z.val).symm.trans
      ((htrack F 1 z).trans (D.homotopy.map_one_left (stageBoundary F z)))
  let bstage := b.comp (⟨Subtype.val, continuous_subtype_val⟩ : C(skeleton n mesh r, Cube n))
  obtain ⟨g, hga, hgc, L, hLa, hLf⟩ := exists_stage_homotopy_paste n mesh r
    (ContinuousMap.id Y) D.endpoint bstage D.homotopy.symm c hc (fun F ↦ (K F).symm)
    (fun F t z ↦ htrack F (unitInterval.symm t) z)
  let J := L.symm
  have hJa (t : unitInterval) (x : skeletonBelow n mesh r) :
      J (t, stageInclusion n mesh r x) = D.homotopy (t, x) := by
    exact (hLa (unitInterval.symm t) x).trans
      (congrArg (fun s ↦ D.homotopy (s, x)) (unitInterval.symm_symm t))
  have hJf (F : StageFace n mesh r) (t : unitInterval) (s : Active F.val → unitInterval) :
      J (t, stageFaceMap F s) = K F (t, s) := by
    exact (hLf F (unitInterval.symm t) s).trans
      (congrArg (fun v ↦ K F (v, s)) (unitInterval.symm_symm t))
  have hchart (W : Set Y) (G : FaceIndex n mesh) (hG : ∀ s, b (face G s) ∈ W)
      (F : StageFace n mesh r) (hFG : faceSet F.val ⊆ faceSet G) :
      ∀ s, (b.comp (face F.val)) s ∈ W := by
    intro s
    obtain ⟨v, hv⟩ := hFG ⟨s, rfl⟩
    change b (face F.val s) ∈ W
    rw [← hv]
    exact hG v
  have hleft (G : FaceIndex n mesh) (hG : ∀ s, b (face G s) ∈ U)
      (t : unitInterval) (x : skeleton n mesh r) (hx : x.val ∈ faceSet G) : J (t, x) ∈ U := by
    obtain ⟨z, rfl⟩ := stageProjection_surjective n mesh r x
    rcases z with x | ⟨F, s⟩
    · rw [show J (t, stageProjection n mesh r (.inl x)) = _ from hJa t x]
      exact D.left_mem G hG t x hx
    · change J (t, stageFaceMap F s) ∈ U
      rw [hJf]
      rcases face_boundary_or_subset_of_mem F.val G s hx with hs | hFG
      · rw [htrack F t ⟨s, hs⟩]
        exact D.left_mem G hG t (stageBoundary F ⟨s, hs⟩) hx
      · exact hU F (hchart U G hG F hFG) t s
  have hright (G : FaceIndex n mesh) (hG : ∀ s, b (face G s) ∈ V)
      (t : unitInterval) (x : skeleton n mesh r) (hx : x.val ∈ faceSet G) : J (t, x) ∈ V := by
    obtain ⟨z, rfl⟩ := stageProjection_surjective n mesh r x
    rcases z with x | ⟨F, s⟩
    · rw [show J (t, stageProjection n mesh r (.inl x)) = _ from hJa t x]
      exact D.right_mem G hG t x hx
    · change J (t, stageFaceMap F s) ∈ V
      rw [hJf]
      rcases face_boundary_or_subset_of_mem F.val G s hx with hs | hFG
      · rw [htrack F t ⟨s, hs⟩]
        exact D.right_mem G hG t (stageBoundary F ⟨s, hs⟩) hx
      · exact hV F (hchart V G hG F hFG) t s
  have hfixed (G : FaceIndex n mesh) (hG : ∀ s, b (face G s) ∈ U ∩ V)
      (t : unitInterval) (x : skeleton n mesh r) (hx : x.val ∈ faceSet G) :
      J (t, x) = b x.val := by
    obtain ⟨z, rfl⟩ := stageProjection_surjective n mesh r x
    rcases z with x | ⟨F, s⟩
    · exact (hJa t x).trans (D.overlap_fixed G hG t x hx)
    · change J (t, stageFaceMap F s) = b (face F.val s)
      rw [hJf]
      rcases face_boundary_or_subset_of_mem F.val G s hx with hs | hFG
      · exact (htrack F t ⟨s, hs⟩).trans
          (D.overlap_fixed G hG t (stageBoundary F ⟨s, hs⟩) hx)
      · exact hfix F (hchart (U ∩ V) G hG F hFG) t s
  have hleftSupport (G : FaceIndex n mesh) (hG : ∀ s, b (face G s) ∈ U)
      (x : skeleton n mesh r) (v : Active G → unitInterval) (hv : face G v = x.val)
      (hx : g x ∉ V) : v ∈ faceThinSupport G a₁ b₁ (p + 1) := by
    obtain ⟨z, rfl⟩ := stageProjection_surjective n mesh r x
    rcases z with x | ⟨F, s⟩
    · exact D.left_support G hG x v hv (by
        change g (stageInclusion n mesh r x) ∉ _ at hx
        rwa [hga] at hx)
    · change g (stageFaceMap F s) ∉ V at hx
      rw [hgc] at hx
      rcases face_boundary_or_subset_of_mem F.val G s ⟨v, hv⟩ with hs | hFG
      · exact D.left_support G hG (stageBoundary F ⟨s, hs⟩) v hv
          (by simpa only [hc F ⟨s, hs⟩] using hx)
      · exact faceThinSupport_of_subset F.val G hFG s v hv.symm a₁ b₁ (p + 1)
          (hSU F (hchart U G hG F hFG) hx)
  have hrightSupport (G : FaceIndex n mesh) (hG : ∀ s, b (face G s) ∈ V)
      (x : skeleton n mesh r) (v : Active G → unitInterval) (hv : face G v = x.val)
      (hx : g x ∉ U) : v ∈ faceThinSupport G a₂ b₂ (q + 1) := by
    obtain ⟨z, rfl⟩ := stageProjection_surjective n mesh r x
    rcases z with x | ⟨F, s⟩
    · exact D.right_support G hG x v hv (by
        change g (stageInclusion n mesh r x) ∉ _ at hx
        rwa [hga] at hx)
    · change g (stageFaceMap F s) ∉ U at hx
      rw [hgc] at hx
      rcases face_boundary_or_subset_of_mem F.val G s ⟨v, hv⟩ with hs | hFG
      · exact D.right_support G hG (stageBoundary F ⟨s, hs⟩) v hv
          (by simpa only [hc F ⟨s, hs⟩] using hx)
      · exact faceThinSupport_of_subset F.val G hFG s v hv.symm a₂ b₂ (q + 1)
          (hSV F (hchart V G hG F hFG) hx)
  let next : C(skeletonBelow n mesh (r + 1), skeleton n mesh r) := {
    toFun x := ⟨x.val, by simpa only [skeletonBelow_succ] using x.property⟩
    continuous_toFun := by fun_prop }
  let D' : TwoChartStageHomotopy n mesh (r + 1) b U V a₁ b₁ a₂ b₂ p q := {
    endpoint := g.comp next
    homotopy := J.compContinuousMap next
    left_mem := fun G h t x hx ↦ hleft G h t (next x) hx
    right_mem := fun G h t x hx ↦ hright G h t (next x) hx
    overlap_fixed := fun G h t x hx ↦ hfixed G h t (next x) hx
    left_support := fun G h x v hv hx ↦ hleftSupport G h (next x) v hv hx
    right_support := fun G h x v hv hx ↦ hrightSupport G h (next x) v hv hx }
  refine ⟨D', ?_⟩
  intro t x y hxy
  change J (t, next y) = _
  exact (congrArg (fun z ↦ J (t, z))
    (show next y = stageInclusion n mesh r x from Subtype.ext hxy.symm)).trans (hJa t x)

end TwoChartStageHomotopy

/-- Simultaneous normalization over the actual finite grid. All original face-chart
constraints, overlap faces, and endpoint support bounds hold in every dimension. -/
theorem exists_two_chart_grid_normalization (n mesh : ℕ) (b : C(Cube n, Y)) (U V : Set Y)
    (a₁ b₁ a₂ b₂ : unitInterval) (hab : a₁ < b₁) (hce : a₂ < b₂) (p q : ℕ)
    (hUV : IsHomotopyConnectedMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C({y : U // y.val ∈ V}, U)) p)
    (hVU : IsHomotopyConnectedMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C({y : V // y.val ∈ U}, V)) q)
    (hcover : ∀ G : FaceIndex n mesh,
      (∀ s, b (face G s) ∈ U) ∨ ∀ s, b (face G s) ∈ V) :
    ∃ g : C(Cube n, Y), ∃ H : b.Homotopy g,
      (∀ G : FaceIndex n mesh, (∀ s, b (face G s) ∈ U) →
        ∀ t s, H (t, face G s) ∈ U) ∧
      (∀ G : FaceIndex n mesh, (∀ s, b (face G s) ∈ V) →
        ∀ t s, H (t, face G s) ∈ V) ∧
      (∀ G : FaceIndex n mesh, (∀ s, b (face G s) ∈ U ∩ V) →
        ∀ t s, H (t, face G s) = b (face G s)) ∧
      (∀ G : FaceIndex n mesh, (∀ s, b (face G s) ∈ U) →
        (g.comp (face G)) ⁻¹' Vᶜ ⊆ faceThinSupport G a₁ b₁ (p + 1)) ∧
      (∀ G : FaceIndex n mesh, (∀ s, b (face G s) ∈ V) →
        (g.comp (face G)) ⁻¹' Uᶜ ⊆ faceThinSupport G a₂ b₂ (q + 1)) := by
  have hstage (r : ℕ) : Nonempty (TwoChartStageHomotopy n mesh r b U V a₁ b₁ a₂ b₂ p q) := by
    induction r with
    | zero => exact ⟨TwoChartStageHomotopy.empty n mesh b U V a₁ b₁ a₂ b₂ p q⟩
    | succ r ih =>
      obtain ⟨D⟩ := ih
      obtain ⟨D', _⟩ := D.exists_succ hab hce hUV hVU hcover
      exact ⟨D'⟩
  obtain ⟨D⟩ := hstage (n + 1)
  let top : C(Cube n, skeletonBelow n mesh (n + 1)) := {
    toFun x := ⟨x, by simp only [skeletonBelow_succ, skeleton_top, Set.mem_univ]⟩
    continuous_toFun := by fun_prop }
  let g := D.endpoint.comp top
  let H : b.Homotopy g := D.homotopy.compContinuousMap top
  refine ⟨g, H, ?_, ?_, ?_, ?_, ?_⟩
  · intro G hG t s
    exact D.left_mem G hG t (top (face G s)) ⟨s, rfl⟩
  · intro G hG t s
    exact D.right_mem G hG t (top (face G s)) ⟨s, rfl⟩
  · intro G hG t s
    exact D.overlap_fixed G hG t (top (face G s)) ⟨s, rfl⟩
  · intro G hG s hs
    exact D.left_support G hG (top (face G s)) s rfl hs
  · intro G hG s hs
    exact D.right_support G hG (top (face G s)) s rfl hs

end Topology.CubicalSubdivision
