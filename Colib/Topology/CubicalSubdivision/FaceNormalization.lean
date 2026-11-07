/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.CubicalSubdivision.FaceThinSupport
public import Colib.Topology.CubicalSubdivision.BoundaryLifting
public import Colib.Topology.CubicalSubdivision.ConnectivityLifting
public import Colib.Topology.Homotopy.Cube.BoundaryHomotopyNormalization

/-!
# Whole-track endpoint normalization in the original face coordinates

The simultaneous-time cube construction is transported only along the actual face-coordinate
homeomorphisms. Its endpoint support estimate then transfers to every incident containing
face, using the unchanged original point. This is the local high-cell step in the grid induction.
-/

/-! Implementation provenance: adapted from
`Quillen/Topology/CubicalSubdivision/FaceNormalization.lean` at commit
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

/-- In the low-dimensional branch, genuine finite connectivity compresses the endpoint
into the supplied subspace while retaining the original boundary track at every time. -/
theorem exists_face_boundary_track_into {n m : ℕ} (F : FaceIndex n m)
    {Y : Type u} [TopologicalSpace Y] (A : Set Y) (q : ℕ)
    (hA : IsHomotopyConnectedMap (⟨Subtype.val, continuous_subtype_val⟩ : C(A, Y)) q)
    (hF : faceDimension F ≤ q) (f : C((Active F → unitInterval), Y))
    (H : C(unitInterval ×
      {x : Active F → unitInterval // x ∈ _root_.Cube.boundary (Active F)}, Y))
    (hzero : ∀ z, H (0, z) = f z.val) (hone : ∀ z, H (1, z) ∈ A) :
    ∃ g : C((Active F → unitInterval), A),
      ∃ K : f.Homotopy ((⟨Subtype.val, continuous_subtype_val⟩ : C(A, Y)).comp g),
        ∀ t z, K (t, z.val) = H (t, z) := by
  let i : C(A, Y) := ⟨Subtype.val, continuous_subtype_val⟩
  let a : C({x : Active F → unitInterval // x ∈ _root_.Cube.boundary (Active F)}, A) :=
    ⟨fun z ↦ ⟨H (1, z), hone z⟩, by fun_prop⟩
  let H' : (i.comp a).Homotopy (f.comp ⟨Subtype.val, continuous_subtype_val⟩) := {
    toFun z := H (unitInterval.symm z.1, z.2)
    continuous_toFun := by fun_prop
    map_zero_left z := by simp only [unitInterval.symm_zero]; rfl
    map_one_left z := by
      change H (unitInterval.symm 1, z) = f z.val
      simpa only [unitInterval.symm_one] using hzero z }
  obtain ⟨g, _, K, hK⟩ := face_fullHELP hA F hF a f H'
  refine ⟨g, K.symm, ?_⟩
  intro t z
  have h := hK (unitInterval.symm t) z
  change K (unitInterval.symm t, z.val) = H (unitInterval.symm (unitInterval.symm t), z) at h
  exact h.trans (congrArg (fun t ↦ H (t, z)) (unitInterval.symm_symm t))

/-- A face endpoint can be normalized with the entire originally specified boundary track
retained at the identical time; the count is measured in its original active coordinates. -/
theorem exists_face_boundary_track_thinSupport {n m : ℕ} (F : FaceIndex n m)
    (a b : unitInterval) (hab : a < b) (p : ℕ) (hp : p ≤ faceDimension F)
    {Y : Type u} [TopologicalSpace Y] (f : C((Active F → unitInterval), Y)) (A : Set Y)
    (H : C(unitInterval ×
      {x : Active F → unitInterval // x ∈ _root_.Cube.boundary (Active F)}, Y))
    (hzero : ∀ z, H (0, z) = f z.val)
    (hboundary : ∀ z, H (1, z) ∈ A → z.val ∈ faceThinSupport F a b p) :
    ∃ g : C((Active F → unitInterval), Y), ∃ K : f.Homotopy g,
      (∀ t z, K (t, z.val) = H (t, z)) ∧ g ⁻¹' A ⊆ faceThinSupport F a b p := by
  let e := faceParamHomeomorph F
  let d := faceParamBoundaryHomeomorph F
  let f' := f.comp e.symm.toHomotopyEquiv.toFun
  let H' : C(unitInterval × Boundary (faceDimension F), Y) :=
    ⟨fun z ↦ H (z.1, d.symm z.2), by fun_prop⟩
  have hz : ∀ z, H' (0, z) = f' z.val := fun z ↦ hzero (d.symm z)
  have hb : ∀ z, H' (1, z) ∈ A → z.val ∈ _root_.Cube.thinSupport a b p := by
    intro z hz
    have h := hboundary (d.symm z) hz
    change (fun j ↦ z.val ((activeEquivFin F) ((activeEquivFin F).symm j))) ∈
      _root_.Cube.thinSupport a b p at h
    simpa only [Equiv.apply_symm_apply] using h
  obtain ⟨g, K, hK, hg⟩ := _root_.Cube.exists_boundary_track_thinSupport
    a b hab p hp f' A H' hz hb
  let g' := g.comp e.toHomotopyEquiv.toFun
  let K' : f.Homotopy g' := {
    toFun z := K (z.1, e z.2)
    continuous_toFun := by fun_prop
    map_zero_left z := (K.map_zero_left (e z)).trans (congrArg f (e.symm_apply_apply z))
    map_one_left z := K.map_one_left (e z) }
  refine ⟨g', K', ?_, ?_⟩
  · intro t z
    have h := hK t (d z)
    change K (t, e z.val) = H (t, d.symm (d z)) at h
    exact h.trans (congrArg (fun z ↦ H (t, z)) (d.symm_apply_apply z))
  · intro x hx
    exact hg hx

/-- Genuine finite connectivity and the high-cell radial construction together normalize
all face dimensions. The supplied boundary support is the only induction invariant needed;
the original boundary track is unchanged in both branches. -/
theorem exists_face_connected_normalization {n m : ℕ} (F : FaceIndex n m)
    (a b : unitInterval) (hab : a < b) {Y : Type u} [TopologicalSpace Y]
    (A : Set Y) (q : ℕ)
    (hA : IsHomotopyConnectedMap (⟨Subtype.val, continuous_subtype_val⟩ : C(A, Y)) q)
    (f : C((Active F → unitInterval), Y))
    (H : C(unitInterval ×
      {x : Active F → unitInterval // x ∈ _root_.Cube.boundary (Active F)}, Y))
    (hzero : ∀ z, H (0, z) = f z.val)
    (hboundary : ∀ z, H (1, z) ∉ A → z.val ∈ faceThinSupport F a b (q + 1)) :
    ∃ g : C((Active F → unitInterval), Y), ∃ K : f.Homotopy g,
      (∀ t z, K (t, z.val) = H (t, z)) ∧ g ⁻¹' Aᶜ ⊆ faceThinSupport F a b (q + 1) := by
  by_cases hF : faceDimension F ≤ q
  · have hone (z : {x : Active F → unitInterval // x ∈ _root_.Cube.boundary (Active F)}) :
        H (1, z) ∈ A := by
      by_contra hz
      exact not_mem_faceThinSupport_of_dimension_lt F a b (q + 1) (by omega) z.val
        (hboundary z hz)
    obtain ⟨g, K, hK⟩ := exists_face_boundary_track_into F A q hA hF f H hzero hone
    refine ⟨(⟨Subtype.val, continuous_subtype_val⟩ : C(A, Y)).comp g, K, hK, ?_⟩
    intro x hx
    exact (hx (g x).property).elim
  · exact exists_face_boundary_track_thinSupport F a b hab (q + 1) (by omega)
      f Aᶜ H hzero hboundary

/-- The normalized endpoint retains the support estimate in every incident containing face.
The actual endpoint map and the entire boundary homotopy are the same as in normalization. -/
theorem exists_face_boundary_track_incident_support {n m : ℕ} (F : FaceIndex n m)
    (a b : unitInterval) (hab : a < b) (p : ℕ) (hp : p ≤ faceDimension F)
    {Y : Type u} [TopologicalSpace Y] (f : C((Active F → unitInterval), Y)) (A : Set Y)
    (H : C(unitInterval ×
      {x : Active F → unitInterval // x ∈ _root_.Cube.boundary (Active F)}, Y))
    (hzero : ∀ z, H (0, z) = f z.val)
    (hboundary : ∀ z, H (1, z) ∈ A → z.val ∈ faceThinSupport F a b p) :
    ∃ g : C((Active F → unitInterval), Y), ∃ K : f.Homotopy g,
      (∀ t z, K (t, z.val) = H (t, z)) ∧
        ∀ (G : FaceIndex n m), faceSet F ⊆ faceSet G →
          ∀ (s : Active F → unitInterval) (t : Active G → unitInterval),
            face F s = face G t → g s ∈ A → t ∈ faceThinSupport G a b p := by
  obtain ⟨g, K, hK, hg⟩ := exists_face_boundary_track_thinSupport F a b hab p hp f A H
    hzero hboundary
  refine ⟨g, K, hK, ?_⟩
  intro G hFG s t h hA
  exact faceThinSupport_of_subset F G hFG s t h a b p (hg hA)

end Topology.CubicalSubdivision
