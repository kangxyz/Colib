/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.CubicalSubdivision.FaceNormalization

/-!
# Connected face normalization inside one original chart

The entire deformation is performed in the actual chart subspace, not just required to end
there. Finite connectivity of its actual overlap inclusion supplies the low-dimensional step;
radial normalization supplies the higher-dimensional step. The original boundary track is
retained, and the endpoint's complement has the actual coordinate-band support bound.
-/

/-! Implementation provenance: adapted from
`Quillen/Topology/CubicalSubdivision/SubspaceNormalization.lean` at commit
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

/-- Normalize inside the original chart while retaining every time of the supplied boundary
track. The connectivity premise concerns its literal overlap inclusion. -/
theorem exists_face_subspace_normalization {n m : ℕ} (F : FaceIndex n m)
    {Y : Type u} [TopologicalSpace Y] (U V : Set Y)
    (a b : unitInterval) (hab : a < b) (q : ℕ)
    (hUV : IsHomotopyConnectedMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C({y : U // y.val ∈ V}, U)) q)
    (f : C((Active F → unitInterval), Y)) (hf : ∀ s, f s ∈ U)
    (H : C(unitInterval ×
      {x : Active F → unitInterval // x ∈ _root_.Cube.boundary (Active F)}, Y))
    (hHU : ∀ t z, H (t, z) ∈ U) (hzero : ∀ z, H (0, z) = f z.val)
    (hboundary : ∀ z, H (1, z) ∉ V → z.val ∈ faceThinSupport F a b (q + 1)) :
    ∃ g : C((Active F → unitInterval), Y), ∃ K : f.Homotopy g,
      (∀ t z, K (t, z.val) = H (t, z)) ∧
      (∀ t s, K (t, s) ∈ U) ∧ g ⁻¹' Vᶜ ⊆ faceThinSupport F a b (q + 1) := by
  let A : Set U := {y | y.val ∈ V}
  let f' : C((Active F → unitInterval), U) := ⟨fun s ↦ ⟨f s, hf s⟩, by fun_prop⟩
  let H' : C(unitInterval ×
      {x : Active F → unitInterval // x ∈ _root_.Cube.boundary (Active F)}, U) :=
    ⟨fun z ↦ ⟨H z, hHU z.1 z.2⟩, by fun_prop⟩
  have hz : ∀ z, H' (0, z) = f' z.val := fun z ↦ Subtype.ext (hzero z)
  obtain ⟨g, K, hK, hg⟩ := exists_face_connected_normalization F a b hab A q hUV f' H' hz
    hboundary
  let i : C(U, Y) := ⟨Subtype.val, continuous_subtype_val⟩
  let g' := i.comp g
  let K' : f.Homotopy g' := {
    toFun z := (K z).val
    continuous_toFun := by fun_prop
    map_zero_left s := congrArg (fun y : U ↦ y.val) (K.map_zero_left s)
    map_one_left s := congrArg (fun y : U ↦ y.val) (K.map_one_left s) }
  refine ⟨g', K', ?_, ?_, ?_⟩
  · intro t z
    exact congrArg (fun y : U ↦ y.val) (hK t z)
  · intro t s
    exact (K (t, s)).property
  · intro s hs
    exact hg hs

end Topology.CubicalSubdivision
