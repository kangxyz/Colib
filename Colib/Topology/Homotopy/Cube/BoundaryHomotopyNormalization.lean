/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.Cube.ThinSupport
public import Colib.Topology.HELP.CubeBoundaryHomeomorph

/-!
# Endpoint thin support retaining the entire supplied boundary homotopy

Cube HEP first extends the specified whole boundary track. Its value at time t is then
precomposed with the boundary-fixed radial map at the same time t. The resulting homotopy
agrees with the original boundary track at every time, while its endpoint has the proved thin
support. No concatenation, time reparameterization, or extra target-space hypothesis is used.
This is the high-dimensional single-cell step for compatible grid normalization.
-/

/-! Implementation provenance: adapted from
`Quillen/Topology/Cube/BoundaryHomotopyNormalization.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, finite bounds,
whole path families and universe parameters are retained in their native owners. -/
@[expose] public section

noncomputable section
open Topology TopCat

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory
open scoped Topology unitInterval

universe u

namespace Cube

variable {d : ℕ} {Y : Type u} [TopologicalSpace Y]

/-- The genuine cube-boundary HEP extends the original unlifted coordinates and the exact
supplied time parameter, for target spaces in any universe. -/
theorem exists_boundary_homotopy_extension (f : C((Fin d → unitInterval), Y))
    (H : C(unitInterval × {x : Fin d → unitInterval // x ∈ _root_.Cube.boundary (Fin d)}, Y))
    (hzero : ∀ z, H (0, z) = f z.val) :
    ∃ J : C(unitInterval × (Fin d → unitInterval), Y),
      (∀ x, J (0, x) = f x) ∧ ∀ t z, J (t, z.val) = H (t, z) := by
  let f' : C(CubicalTests.cube.{u} d, Y) := ⟨fun x ↦ f x.down, by fun_prop⟩
  let H' : C(unitInterval × CubicalTests.boundary.{u} d, Y) :=
    ⟨fun z ↦ H (z.1, ⟨z.2.val.down, z.2.property⟩), by fun_prop⟩
  obtain ⟨J, hJzero, hJ⟩ := homotopyExtensionProperty_continuous
    (CubicalTests.boundaryInclusion_hep d) (TopCat.of Y) f' H'
    (fun z ↦ hzero ⟨z.val.down, z.property⟩)
  refine ⟨⟨fun z ↦ J (z.1, ULift.up z.2), by fun_prop⟩, ?_, ?_⟩
  · intro x
    exact hJzero (ULift.up x)
  · intro t z
    exact hJ t ⟨ULift.up z.val, z.property⟩

/-- Perform the original extension and the radial homotopy simultaneously, with identical
original time coordinates. -/
def simultaneousBandNormalization (a b : unitInterval) (hab : a < b)
    (J : C(unitInterval × (Fin d → unitInterval), Y)) :
    C(unitInterval × (Fin d → unitInterval), Y) where
  toFun z := J (z.1, bandExpansionHomotopy a b hab (z.1, z.2))
  continuous_toFun := J.continuous.comp
    (continuous_fst.prodMk (bandExpansionHomotopy a b hab).continuous)

/-- Simultaneous normalization does not change the original initial map. -/
theorem simultaneousBandNormalization_zero (a b : unitInterval) (hab : a < b)
    (J : C(unitInterval × (Fin d → unitInterval), Y)) (x : Fin d → unitInterval) :
    simultaneousBandNormalization a b hab J (0, x) = J (0, x) := by
  change J (0, bandExpansionHomotopy a b hab (0, x)) = J (0, x)
  exact congrArg (fun x ↦ J (0, x)) ((bandExpansionHomotopy a b hab).map_zero_left x)

/-- Every boundary value is unchanged at the identical arbitrary time. -/
theorem simultaneousBandNormalization_boundary (a b : unitInterval) (hab : a < b)
    (J : C(unitInterval × (Fin d → unitInterval), Y)) (t : unitInterval)
    (x : Fin d → unitInterval) (hx : x ∈ _root_.Cube.boundary (Fin d)) :
    simultaneousBandNormalization a b hab J (t, x) = J (t, x) := by
  change J (t, bandExpansionHomotopy a b hab (t, x)) = J (t, x)
  exact congrArg (fun x ↦ J (t, x)) ((bandExpansionHomotopy a b hab).prop t x hx)

/-- The endpoint is the original extension endpoint precomposed with the explicit radial map. -/
theorem simultaneousBandNormalization_one (a b : unitInterval) (hab : a < b)
    (J : C(unitInterval × (Fin d → unitInterval), Y)) (x : Fin d → unitInterval) :
    simultaneousBandNormalization a b hab J (1, x) = J (1, bandExpansion a b hab x) := by
  change J (1, bandExpansionHomotopy a b hab (1, x)) = J (1, bandExpansion a b hab x)
  exact congrArg (fun x ↦ J (1, x)) ((bandExpansionHomotopy a b hab).map_one_left x)

/-- Endpoint thin support can be achieved while retaining the supplied whole boundary track,
including zero dimension and the extreme coordinate counts. -/
theorem exists_boundary_track_thinSupport (a b : unitInterval) (hab : a < b)
    (p : ℕ) (hp : p ≤ d) (f : C((Fin d → unitInterval), Y)) (A : Set Y)
    (H : C(unitInterval × {x : Fin d → unitInterval // x ∈ _root_.Cube.boundary (Fin d)}, Y))
    (hzero : ∀ z, H (0, z) = f z.val)
    (hboundary : ∀ z, H (1, z) ∈ A → z.val ∈ thinSupport a b p) :
    ∃ g : C((Fin d → unitInterval), Y), ∃ K : f.Homotopy g,
      (∀ t z, K (t, z.val) = H (t, z)) ∧ g ⁻¹' A ⊆ thinSupport a b p := by
  obtain ⟨J, hJzero, hJ⟩ := exists_boundary_homotopy_extension f H hzero
  let g₀ : C((Fin d → unitInterval), Y) := ⟨fun x ↦ J (1, x), by fun_prop⟩
  let g := g₀.comp (bandExpansion a b hab)
  let K : f.Homotopy g := {
    toContinuousMap := simultaneousBandNormalization a b hab J
    map_zero_left x := (simultaneousBandNormalization_zero a b hab J x).trans (hJzero x)
    map_one_left x := simultaneousBandNormalization_one a b hab J x }
  refine ⟨g, K, ?_, ?_⟩
  · intro t z
    exact (simultaneousBandNormalization_boundary a b hab J t z.val z.property).trans (hJ t z)
  · apply preimage_subset_thinSupport a b hab p hp g₀ A
    intro x hx hAx
    apply hboundary ⟨x, hx⟩
    exact (hJ 1 ⟨x, hx⟩) ▸ hAx

end Cube
