/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.MetricOrderComplex.AffineSegment

/-!
# The actual diagonal-fixed common-support connector

On the open positive-common-mass domain, move linearly from the first point to
its normalized common point, then linearly to the second point. Each half stays
in its own original chain simplex; the union of the two original supports need
not be a chain. The connector is jointly continuous in the actual L1 topology,
fixes the whole diagonal, and preserves every shared open vertex star.
-/

/-! Implementation source: `Quillen/Topology/MetricOrderComplex/Equiconnection.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual finitely supported
coordinate model, L1 topology and universe parameters are retained. -/
@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open scoped Topology unitInterval

universe u
namespace Topology.MetricOrderComplex

variable {P : Type u} [PartialOrder P]

/-- Classical equality is used only to enumerate finite supports. -/
local instance instDecidableEqEquiconnection : DecidableEq P := Classical.decEq P

/-- The first segment lies in the first original support simplex. -/
theorem commonPoint_left_chain (x y : MetricOrderComplex P) (h : 0 < commonMass x y) :
    IsChain (· ≤ ·) ((x.weights.support ∪ (commonPoint x y h).weights.support :
      Finset P) : Set P) := by
  rw [commonPoint_support, Finset.union_eq_left.mpr Finset.inter_subset_left]
  exact x.support_chain

/-- The second segment lies in the second original support simplex. -/
theorem commonPoint_right_chain (x y : MetricOrderComplex P) (h : 0 < commonMass x y) :
    IsChain (· ≤ ·) (((commonPoint x y h).weights.support ∪ y.weights.support :
      Finset P) : Set P) := by
  rw [commonPoint_support, Finset.union_eq_right.mpr Finset.inter_subset_right]
  exact y.support_chain

/-- The actual two-segment connector between a pair with positive common mass. -/
def connectorPath (x y : MetricOrderComplex P) (h : 0 < commonMass x y) : Path x y :=
  (affinePath x (commonPoint x y h) (commonPoint_left_chain x y h)).trans
    (affinePath (commonPoint x y h) y (commonPoint_right_chain x y h))

/-- The connector fixes every point of the whole diagonal. -/
@[simp]
theorem connectorPath_self (x : MetricOrderComplex P) (h : 0 < commonMass x x) :
    connectorPath x x h = Path.refl x := by
  have hh (m : MetricOrderComplex P) (hm : m = x) (h₁) (h₂) :
      (affinePath x m h₁).trans (affinePath m x h₂) = Path.refl x := by
    subst m
    simp only [affinePath_self, Path.refl_trans_refl]
  exact hh _ (commonPoint_self x h) _ _

/-- Concatenating the actual continuous segment families gives joint L1 continuity. -/
@[fun_prop]
theorem connectorPath_continuous_family :
    Continuous (fun z : OverlappingPairs P × I ↦
      connectorPath z.1.1.1 z.1.1.2 z.1.2 z.2) := by
  let f : C(OverlappingPairs P, MetricOrderComplex P) :=
    ⟨fun z ↦ z.1.1, continuous_fst.comp continuous_subtype_val⟩
  let g : C(OverlappingPairs P, MetricOrderComplex P) :=
    ⟨fun z ↦ z.1.2, continuous_snd.comp continuous_subtype_val⟩
  exact Path.trans_continuous_family (a := fun z : OverlappingPairs P ↦ z.1.1)
    (b := commonPointMap) (c := fun z : OverlappingPairs P ↦ z.1.2)
    (fun z ↦ affinePath z.1.1 (commonPointMap z) (commonPoint_left_chain _ _ z.2))
    (affinePath_continuous_family f commonPointMap
      (fun z ↦ commonPoint_left_chain _ _ z.2))
    (fun z ↦ affinePath (commonPointMap z) z.1.2 (commonPoint_right_chain _ _ z.2))
    (affinePath_continuous_family commonPointMap g
      (fun z ↦ commonPoint_right_chain _ _ z.2))

/-- The continuous connector on its original open diagonal neighborhood. -/
def connector : C(OverlappingPairs P × I, MetricOrderComplex P) :=
  ⟨fun z ↦ connectorPath z.1.1.1 z.1.1.2 z.1.2 z.2, connectorPath_continuous_family⟩

@[simp]
theorem connector_zero (z : OverlappingPairs P) : connector (z, 0) = z.1.1 :=
  (connectorPath z.1.1 z.1.2 z.2).source

@[simp]
theorem connector_one (z : OverlappingPairs P) : connector (z, 1) = z.1.2 :=
  (connectorPath z.1.1 z.1.2 z.2).target

@[simp]
theorem connector_diagonal (x : MetricOrderComplex P) (t : I) :
    connector (⟨(x, x), by simp⟩, t) = x := by
  change connectorPath x x _ t = x
  rw [connectorPath_self]
  rfl

/-- A common positive coordinate stays positive through both halves of the connector. -/
theorem connectorPath_coordinate_pos (x y : MetricOrderComplex P) (h : 0 < commonMass x y)
    (v : P) (hx : 0 < x.weights v) (hy : 0 < y.weights v) (t : I) :
    0 < (connectorPath x y h t).weights v := by
  have hm : 0 < (commonPoint x y h).weights v := by
    rw [commonPoint_weights]
    exact div_pos (lt_min hx hy) h
  have hr := Set.mem_range_self (f := connectorPath x y h) t
  rw [connectorPath, Path.trans_range] at hr
  rcases hr with ⟨s, hs⟩ | ⟨s, hs⟩
  · change _ = connectorPath x y h t at hs
    rw [← hs]
    exact affineCombination_coordinate_pos s x (commonPoint x y h)
      (commonPoint_left_chain x y h) v hx hm
  · change _ = connectorPath x y h t at hs
    rw [← hs]
    exact affineCombination_coordinate_pos s (commonPoint x y h) y
      (commonPoint_right_chain x y h) v hm hy

/-- The open vertex star in the actual metric order complex. -/
def vertexStar (v : P) : Set (MetricOrderComplex P) := {x | 0 < x.weights v}

/-- Every vertex star is open in the actual L1 metric. -/
theorem isOpen_vertexStar (v : P) : IsOpen (vertexStar v) :=
  isOpen_lt continuous_const (continuous_coordinate v)

/-- The stars cover every metric point, with no local-finiteness assumption on the poset. -/
theorem exists_mem_vertexStar (x : MetricOrderComplex P) : ∃ v, x ∈ vertexStar v := by
  obtain ⟨v, hv⟩ := x.support_nonempty
  exact ⟨v, lt_of_le_of_ne (x.weights_nonneg v) (Ne.symm (Finsupp.mem_support_iff.mp hv))⟩

/-- Two points in one vertex star belong to the connector domain. -/
theorem commonMass_pos_of_mem_vertexStar {v : P} {x y : MetricOrderComplex P}
    (hx : x ∈ vertexStar v) (hy : y ∈ vertexStar v) : 0 < commonMass x y := by
  apply (commonMass_pos_iff_support x y).mpr
  exact ⟨v, Finset.mem_inter.mpr
    ⟨Finsupp.mem_support_iff.mpr (ne_of_gt hx), Finsupp.mem_support_iff.mpr (ne_of_gt hy)⟩⟩

/-- The open star is genuinely connector-convex at every interpolation time. -/
theorem connector_mem_vertexStar {v : P} {x y : MetricOrderComplex P}
    (hx : x ∈ vertexStar v) (hy : y ∈ vertexStar v) (t : I) :
    connectorPath x y (commonMass_pos_of_mem_vertexStar hx hy) t ∈ vertexStar v :=
  connectorPath_coordinate_pos x y _ v hx hy t

end Topology.MetricOrderComplex
