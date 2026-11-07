/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.MetricOrderComplex.CutoffRealization
public import Colib.Topology.MetricOrderComplex.CutoffHomotopy
public import Colib.Topology.Realization.CylinderContinuity
public import Colib.Topology.Homotopy.Equiv.Based
public import Mathlib.Topology.Homotopy.Equiv

/-!
# Vertex-fixed weak/strong order-complex homotopy equivalence

The forward map is the original realization coordinate map. The reverse map
reconstructs the half-maximum cutoff, and both inverse homotopies use the
explicit affine cutoff blend. The weak-target homotopy is continuous on each
fixed finite-chain cylinder and descends through the actual preserved
realization colimit. Both homotopies retain every vertex.
-/

/-! Implementation source: `Quillen/Topology/MetricOrderComplex/RealizationHomotopyEquiv.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The pinned native realization and
its standard-simplex coordinates are unchanged. -/
@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Convexity SSet Opposite
open scoped Simplicial Topology unitInterval

universe u

namespace Topology.MetricOrderComplex

variable {P : Type u} [PartialOrder P]

/-- The pointwise affine cutoff blend reconstructed in the original weak realization. -/
def realizationCutoffBlend (t : I) (z : |nerve P|) : |nerve P| :=
  realizationReconstruction (cutoffBlend t (realizationCoordinates z))

/-- On each original simplex, the whole interpolation remains in one fixed finite chain. -/
theorem continuous_realizationCutoffBlend_simplex {n : SimplexCategory}
    (s : (nerve P).obj (op n)) :
    Continuous (fun z : I × StdSimplex ℝ (Fin (n.len + 1)) ↦
      realizationCutoffBlend z.1 (realizationSimplex s z.2)) := by
  have hc : Continuous (fun z : I × StdSimplex ℝ (Fin (n.len + 1)) ↦
      (z.1, simplexCoordinates s z.2)) :=
    continuous_fst.prodMk ((simplexCoordinates s).continuous.comp continuous_snd)
  let f : C(I × StdSimplex ℝ (Fin (n.len + 1)), MetricOrderComplex P) :=
    cutoffHomotopy.toContinuousMap.comp ⟨fun z ↦ (z.1, simplexCoordinates s z.2), hc⟩
  have hf : ∀ z, ((f z).weights.support : Set P) ⊆ Set.range s.obj := by
    intro z v hv
    change v ∈ (cutoffBlend z.1 (simplexCoordinates s z.2)).weights.support at hv
    have hv' : v ∈ (simplexCoordinates s z.2).weights.support :=
      cutoffBlend_support_subset z.1 (simplexCoordinates s z.2) hv
    have hr := (mem_range_simplexCoordinates s (simplexCoordinates s z.2)).mp ⟨z.2, rfl⟩
    exact hr hv'
  simpa only [realizationCutoffBlend, realizationCoordinates_simplex, f,
    ContinuousMap.comp_apply, cutoffHomotopy, ContinuousMap.coe_mk] using
    continuous_reconstruction_of_support_subset s f hf

/-- The weak interpolation is continuous through the original realization cylinder colimit. -/
@[fun_prop]
theorem continuous_realizationCutoffBlend :
    Continuous (fun z : I × |nerve P| ↦ realizationCutoffBlend z.1 z.2) := by
  apply (continuous_realizationCylinder_iff _).mpr
  intro n s
  exact continuous_realizationCutoffBlend_simplex s

@[simp]
theorem realizationCutoffBlend_zero (z : |nerve P|) :
    realizationCutoffBlend 0 z = cutoffRealizationMap (realizationCoordinates z) := by
  simp only [realizationCutoffBlend, cutoffBlend_zero]
  rfl

@[simp]
theorem realizationCutoffBlend_one (z : |nerve P|) : realizationCutoffBlend 1 z = z := by
  simp only [realizationCutoffBlend, cutoffBlend_one, realizationReconstruction_coordinates]

@[simp]
theorem realizationCutoffBlend_vertex (t : I) (p : P) :
    realizationCutoffBlend t (classifyingSpacePoint.{u, u} p) = classifyingSpacePoint.{u, u} p := by
  simp only [realizationCutoffBlend, realizationCoordinates_vertex, cutoffBlend_vertex,
    realizationReconstruction_vertex]

/-- The actual weak-realization-side inverse homotopy. -/
def realizationCutoffHomotopy :
    ((cutoffRealizationMap (P := P)).comp realizationCoordinates).Homotopy
      (ContinuousMap.id |nerve P|) where
  toFun z := realizationCutoffBlend z.1 z.2
  continuous_toFun := continuous_realizationCutoffBlend
  map_zero_left := realizationCutoffBlend_zero
  map_one_left := realizationCutoffBlend_one

/-- The actual metric-side inverse homotopy is the already-proved metric cutoff homotopy. -/
def metricCutoffInverseHomotopy :
    ((realizationCoordinates (P := P)).comp cutoffRealizationMap).Homotopy
      (ContinuousMap.id (MetricOrderComplex P)) where
  toFun := cutoffHomotopy
  continuous_toFun := cutoffHomotopy.continuous
  map_zero_left x := by
    rw [cutoffHomotopy.apply_zero]
    exact (realizationCoordinates_cutoffRealization x).symm
  map_one_left := cutoffHomotopy.apply_one

/-- The actual weak realization and its L1 model are homotopy equivalent. -/
def realizationHomotopyEquiv : ContinuousMap.HomotopyEquiv |nerve P| (MetricOrderComplex P) where
  toFun := realizationCoordinates
  invFun := cutoffRealizationMap
  left_inv := ⟨realizationCutoffHomotopy⟩
  right_inv := ⟨metricCutoffInverseHomotopy⟩

@[simp]
theorem realizationHomotopyEquiv_toFun :
    (realizationHomotopyEquiv (P := P)).toFun = realizationCoordinates := rfl

/-- The weak/strong homotopy equivalence retains an arbitrary chosen original vertex. -/
def basedRealizationHomotopyEquiv (p : P) :
    BasedHomotopyEquiv (classifyingSpacePoint.{u, u} p) (vertex p) where
  toMap := realizationCoordinates
  invMap := cutoffRealizationMap
  map_point := realizationCoordinates_vertex p
  inv_point := cutoffRealizationMap_vertex p
  leftHomotopy := realizationCutoffHomotopy
  rightHomotopy := metricCutoffInverseHomotopy
  left_fixed t := realizationCutoffBlend_vertex t p
  right_fixed t := cutoffHomotopy_vertex t p

@[simp]
theorem basedRealizationHomotopyEquiv_toMap (p : P) :
    (basedRealizationHomotopyEquiv p).toMap = realizationCoordinates := rfl

end Topology.MetricOrderComplex
