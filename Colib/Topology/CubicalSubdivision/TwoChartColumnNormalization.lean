/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.CubicalSubdivision.TwoChartGridNormalization
public import Colib.Topology.CubicalSubdivision.ColumnAvoidance
public import Colib.Topology.CubicalSubdivision.FaceCover
public import Colib.Topology.CubicalSubdivision.CoordinateFaces

/-!
# Actual two-chart normalization and vertical-column avoidance

A single sufficiently fine product grid supports the proved whole-face induction. Its endpoint
satisfies the two thin-support estimates on every original affine cell. The same horizontal
coordinate representative is then used at arbitrary different path times in different vertical
cells. For parameter dimension `d < p + q`, each resulting vertical path stays in one chart.
The path cube has dimension `d + 1`; the original chart and overlap-face tracks are retained.
-/

/-! Implementation provenance: adapted from
`Quillen/Topology/CubicalSubdivision/TwoChartColumnNormalization.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, finite bounds,
whole path families and universe parameters are retained in their native owners. -/
@[expose] public section

noncomputable section
open Topology TopCat

open scoped Topology unitInterval

universe u

namespace Topology.CubicalSubdivision

/-- Intrinsic moving-coordinate support gives the identical count in the full coordinate
family, without assuming the face is full-dimensional. -/
theorem thinSupport_of_faceThinSupport {n mesh : ℕ} (G : FaceIndex n mesh)
    (a b : unitInterval) (p : ℕ) (s : Cube n)
    (hs : (fun i : Active G ↦ s i.val) ∈ faceThinSupport G a b p) :
    s ∈ _root_.Cube.thinSupport a b p := by
  let e : Fin (faceDimension G) ↪ Fin n :=
    (activeEquivFin G).symm.toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩
  exact _root_.Cube.thinSupport_of_coordinateEmbedding a b e s p hs

/-- A fine original grid normalizes the actual path cube so every vertical column lies in
one original open chart. All originally subordinate faces remain in their chart at every time,
and original overlap faces remain fixed. The two finite bounds concern actual overlap maps. -/
theorem exists_two_chart_column_normalization (d : ℕ) {Y : Type u} [TopologicalSpace Y]
    (b : C(Cube (d + 1), Y)) (U V : Set Y) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : ∀ x, b x ∈ U ∪ V)
    (a₁ b₁ a₂ b₂ : unitInterval) (hab : a₁ < b₁) (hbc : b₁ ≤ a₂) (hce : a₂ < b₂)
    (p q : ℕ) (hd : d < p + q)
    (hUV : IsHomotopyConnectedMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C({y : U // y.val ∈ V}, U)) p)
    (hVU : IsHomotopyConnectedMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C({y : V // y.val ∈ U}, V)) q) :
    ∃ mesh : ℕ, ∃ g : C(Cube (d + 1), Y), ∃ H : b.Homotopy g,
      (∀ G : FaceIndex (d + 1) mesh,
        (∀ s, b (face G s) ∈ U) ∨ ∀ s, b (face G s) ∈ V) ∧
      (∀ G : FaceIndex (d + 1) mesh, (∀ s, b (face G s) ∈ U) →
        ∀ t s, H (t, face G s) ∈ U) ∧
      (∀ G : FaceIndex (d + 1) mesh, (∀ s, b (face G s) ∈ V) →
        ∀ t s, H (t, face G s) ∈ V) ∧
      (∀ G : FaceIndex (d + 1) mesh, (∀ s, b (face G s) ∈ U ∩ V) →
        ∀ t s, H (t, face G s) = b (face G s)) ∧
      (∀ k, (g.comp (cell (d + 1) mesh k)) ⁻¹' (U \ V) ⊆
        _root_.Cube.thinSupport a₁ b₁ (p + 1)) ∧
      (∀ k, (g.comp (cell (d + 1) mesh k)) ⁻¹' (V \ U) ⊆
        _root_.Cube.thinSupport a₂ b₂ (q + 1)) ∧
      ∀ x : Cube d, (∀ t, g (Fin.cons t x) ∈ U) ∨ ∀ t, g (Fin.cons t x) ∈ V := by
  let W : Bool → Set Y := fun j ↦ if j then U else V
  have hW (j : Bool) : IsOpen (W j) := by cases j <;> assumption
  have hWcover (x : Cube (d + 1)) : ∃ j, b x ∈ W j := by
    rcases hcover x with hx | hx
    · exact ⟨true, hx⟩
    · exact ⟨false, hx⟩
  obtain ⟨mesh, hm⟩ := exists_grid_faces_subordinate (d + 1) b W hW hWcover
  have hfaces (G : FaceIndex (d + 1) mesh) :
      (∀ s, b (face G s) ∈ U) ∨ ∀ s, b (face G s) ∈ V := by
    obtain ⟨j, hj⟩ := hm G
    cases j
    · exact Or.inr hj
    · exact Or.inl hj
  obtain ⟨g, H, hHU, hHV, hfix, hSU, hSV⟩ := exists_two_chart_grid_normalization
    (d + 1) mesh b U V a₁ b₁ a₂ b₂ hab hce p q hUV hVU hfaces
  have hcellU (k : CellIndex (d + 1) mesh) :
      (g.comp (cell (d + 1) mesh k)) ⁻¹' (U \ V) ⊆
        _root_.Cube.thinSupport a₁ b₁ (p + 1) := by
    intro s hs
    let v : Active (maximalFace k) → unitInterval := fun i ↦ s i.val
    have hv : face (maximalFace k) v = cell (d + 1) mesh k s := maximalFace_apply k s
    rcases hfaces (maximalFace k) with hG | hG
    · apply thinSupport_of_faceThinSupport (maximalFace k) a₁ b₁ (p + 1) s
      apply hSU (maximalFace k) hG
      change g (face (maximalFace k) v) ∉ V
      rw [hv]
      exact hs.2
    · have h := hHV (maximalFace k) hG 1 v
      have he : H (1, face (maximalFace k) v) = g (cell (d + 1) mesh k s) :=
        (H.map_one_left _).trans (congrArg g hv)
      exact (hs.2 (he ▸ h)).elim
  have hcellV (k : CellIndex (d + 1) mesh) :
      (g.comp (cell (d + 1) mesh k)) ⁻¹' (V \ U) ⊆
        _root_.Cube.thinSupport a₂ b₂ (q + 1) := by
    intro s hs
    let v : Active (maximalFace k) → unitInterval := fun i ↦ s i.val
    have hv : face (maximalFace k) v = cell (d + 1) mesh k s := maximalFace_apply k s
    rcases hfaces (maximalFace k) with hG | hG
    · have h := hHU (maximalFace k) hG 1 v
      have he : H (1, face (maximalFace k) v) = g (cell (d + 1) mesh k s) :=
        (H.map_one_left _).trans (congrArg g hv)
      exact (hs.2 (he ▸ h)).elim
    · apply thinSupport_of_faceThinSupport (maximalFace k) a₂ b₂ (q + 1) s
      apply hSV (maximalFace k) hG
      change g (face (maximalFace k) v) ∉ U
      rw [hv]
      exact hs.2
  have hgcover (x : Cube (d + 1)) : g x ∈ U ∪ V := by
    obtain ⟨k, s, rfl⟩ := cell_covers (d + 1) mesh x
    let v : Active (maximalFace k) → unitInterval := fun i ↦ s i.val
    have he : H (1, face (maximalFace k) v) = g (cell (d + 1) mesh k s) :=
      (H.map_one_left _).trans (congrArg g (maximalFace_apply k s))
    rcases hfaces (maximalFace k) with hG | hG
    · exact Or.inl (he ▸ hHU (maximalFace k) hG 1 v)
    · exact Or.inr (he ▸ hHV (maximalFace k) hG 1 v)
  exact ⟨mesh, g, H, hfaces, hHU, hHV, hfix, hcellU, hcellV,
    grid_column_image_subset_one d mesh a₁ b₁ a₂ b₂ hbc p q hd g U V hgcover hcellU hcellV⟩

/-- Normalize an actual family of paths with endpoints in the two charts. The complete
original path at every boundary parameter stays pointwise unchanged whenever its image is in
the overlap. No time reparameterization is introduced on that boundary. -/
theorem exists_relative_two_chart_column_normalization
    (d : ℕ) {Y : Type u} [TopologicalSpace Y]
    (b : C(Cube (d + 1), Y)) (U V : Set Y) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : ∀ x, b x ∈ U ∪ V)
    (hleft : ∀ x, b (Fin.cons 0 x) ∈ U) (hright : ∀ x, b (Fin.cons 1 x) ∈ V)
    (hboundary : ∀ t x, x ∈ _root_.Cube.boundary (Fin d) → b (Fin.cons t x) ∈ U ∩ V)
    (a₁ b₁ a₂ b₂ : unitInterval) (hab : a₁ < b₁) (hbc : b₁ ≤ a₂) (hce : a₂ < b₂)
    (p q : ℕ) (hd : d < p + q)
    (hUV : IsHomotopyConnectedMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C({y : U // y.val ∈ V}, U)) p)
    (hVU : IsHomotopyConnectedMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C({y : V // y.val ∈ U}, V)) q) :
    ∃ g : C(Cube (d + 1), Y), ∃ H : b.Homotopy g,
      (∀ r x, H (r, Fin.cons 0 x) ∈ U) ∧
      (∀ r x, H (r, Fin.cons 1 x) ∈ V) ∧
      (∀ r t x, x ∈ _root_.Cube.boundary (Fin d) →
        H (r, Fin.cons t x) = b (Fin.cons t x)) ∧
      ∀ x : Cube d, (∀ t, g (Fin.cons t x) ∈ U) ∨ ∀ t, g (Fin.cons t x) ∈ V := by
  obtain ⟨mesh, g, H, _, hHU, hHV, hfix, _, _, hcolumn⟩ :=
    exists_two_chart_column_normalization d b U V hU hV hcover
      a₁ b₁ a₂ b₂ hab hbc hce p q hd hUV hVU
  refine ⟨g, H, ?_, ?_, ?_, hcolumn⟩
  · intro r x
    obtain ⟨G, s, hs, hG⟩ := exists_face_in_coordinate_zero (d + 1) mesh 0 (Fin.cons 0 x) rfl
    have h : ∀ v, b (face G v) ∈ U := by
      intro v
      have he : Fin.cons 0 (Fin.tail (face G v)) = face G v := by
        rw [← hG v]
        exact Fin.cons_self_tail _
      exact he ▸ hleft (Fin.tail (face G v))
    exact hs ▸ hHU G h r s
  · intro r x
    obtain ⟨G, s, hs, hG⟩ := exists_face_in_coordinate_one (d + 1) mesh 0 (Fin.cons 1 x) rfl
    have h : ∀ v, b (face G v) ∈ V := by
      intro v
      have he : Fin.cons 1 (Fin.tail (face G v)) = face G v := by
        rw [← hG v]
        exact Fin.cons_self_tail _
      exact he ▸ hright (Fin.tail (face G v))
    exact hs ▸ hHV G h r s
  · intro r t x hx
    obtain ⟨i, hi⟩ := hx
    have hface : ∃ G : FaceIndex (d + 1) mesh, ∃ s : Active G → unitInterval,
        face G s = Fin.cons t x ∧ ∀ v, (Fin.tail (face G v)) ∈ _root_.Cube.boundary (Fin d) := by
      rcases hi with hi | hi
      · obtain ⟨G, s, hs, hG⟩ := exists_face_in_coordinate_zero (d + 1) mesh i.succ
          (Fin.cons t x) hi
        exact ⟨G, s, hs, fun v ↦ ⟨i, Or.inl (hG v)⟩⟩
      · obtain ⟨G, s, hs, hG⟩ := exists_face_in_coordinate_one (d + 1) mesh i.succ
          (Fin.cons t x) hi
        exact ⟨G, s, hs, fun v ↦ ⟨i, Or.inr (hG v)⟩⟩
    obtain ⟨G, s, hs, hG⟩ := hface
    have h : ∀ v, b (face G v) ∈ U ∩ V := by
      intro v
      exact (Fin.cons_self_tail (face G v)) ▸
        hboundary ((face G v) 0) (Fin.tail (face G v)) (hG v)
    exact hs ▸ hfix G h r s

end Topology.CubicalSubdivision
