/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.MetricOrderComplex.FiniteCharts
public import Colib.Topology.MetricOrderComplex.Cutoff

/-!
# A continuous cutoff map into the original weak realization

Reconstruct the normalized half-maximum cutoff. Near each metric point its
support lies in that point's one fixed finite chain, where reconstruction is
continuous. This proves actual continuity from the L1 model to the weak
realization without asserting continuity of the unmodified set inverse.
-/

/-! Implementation source: `Quillen/Topology/MetricOrderComplex/CutoffRealization.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The pinned native realization and
its standard-simplex coordinates are unchanged. -/
@[expose] public section
noncomputable section

open CategoryTheory
open scoped Simplicial Topology

universe u

namespace Topology.MetricOrderComplex

variable {P : Type u} [PartialOrder P]

/-- Reconstruct the locally supported cutoff in the original realization. -/
def cutoffRealization (x : MetricOrderComplex P) : |nerve P| :=
  realizationReconstruction x.cutoff

/-- The cutoff is continuous into the weak realization by local finite-chart factorization. -/
@[fun_prop]
theorem continuous_cutoffRealization : Continuous (cutoffRealization (P := P)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨n, s, _, _, hr, _, _⟩ := exists_strict_representation x
  let U := Metric.ball x (x.maximum / 4)
  have hU : U ∈ 𝓝 x := Metric.ball_mem_nhds x (div_pos x.maximum_pos (by norm_num))
  let f : C(U, MetricOrderComplex P) :=
    ⟨fun y ↦ y.1.cutoff, continuous_cutoff.comp continuous_subtype_val⟩
  have hf : ∀ y : U, ((f y).weights.support : Set P) ⊆ Set.range s.obj := by
    intro y
    rw [hr]
    exact cutoff_support_subset_of_dist_lt x y.1 y.2
  have hc : Continuous (fun y : U ↦ cutoffRealization y.1) :=
    continuous_reconstruction_of_support_subset s f hf
  exact (continuousOn_iff_continuous_domRestrict.mpr hc).continuousAt hU

/-- The actual continuous map from metric coordinates to the weak realization. -/
def cutoffRealizationMap : C(MetricOrderComplex P, |nerve P|) :=
  ⟨cutoffRealization, continuous_cutoffRealization⟩

/-- Taking coordinates after the weak-target map gives exactly the original metric cutoff. -/
@[simp]
theorem realizationCoordinates_cutoffRealization (x : MetricOrderComplex P) :
    realizationCoordinates (cutoffRealizationMap x) = x.cutoff :=
  realizationCoordinates_reconstruction x.cutoff

/-- Every possible original vertex is retained by the cutoff-to-realization map. -/
@[simp]
theorem cutoffRealizationMap_vertex (p : P) :
    cutoffRealizationMap (vertex p) = classifyingSpacePoint.{u, u} p := by
  change realizationReconstruction (vertex p).cutoff = _
  rw [cutoff_vertex, realizationReconstruction_vertex]

end Topology.MetricOrderComplex
