/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.MetricOrderComplex.CommonPoint
public import Mathlib.Topology.ContinuousMap.Basic

import Mathlib.Tactic.Linarith

/-!
# Actual L1 continuity of normalized common points

At a fixed center x, the common-mass sum can be taken over the one finite
support of x. The identity dist(x,y)=2-2*commonMass(x,y) therefore controls
the entire L1 distance using finitely many coordinates of y, including its
varying tail. This proves a coordinate continuity criterion for these positive
total-one distributions; no such criterion is assumed for general L1 vectors.
Normalization then gives a continuous common point on the open overlap domain.
-/

/-! Implementation source: `Quillen/Topology/MetricOrderComplex/CommonPointContinuity.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual finitely supported
coordinate model, L1 topology and universe parameters are retained. -/
@[expose] public section
noncomputable section

open scoped Topology

universe u v
namespace Topology.MetricOrderComplex

variable {P : Type u} [PartialOrder P]

/-- The common-mass sum needs only the fixed support of its first point. -/
theorem commonMass_eq_sum_left (x y : MetricOrderComplex P) :
    commonMass x y = ∑ v ∈ x.weights.support, min (x.weights v) (y.weights v) := by
  classical
  have hs : (commonWeights x y).support ⊆ x.weights.support := by
    rw [commonWeights_support]
    exact Finset.inter_subset_left
  rw [commonMass, Finsupp.sum_of_support_subset _ hs (fun _ a ↦ a) (by simp)]
  rfl

/-- Positive total-one mass makes coordinate continuity imply genuine L1 continuity. -/
theorem continuous_of_coordinates {A : Type v} [TopologicalSpace A]
    (f : A → MetricOrderComplex P)
    (hf : ∀ v, Continuous (fun a ↦ (f a).weights v)) : Continuous f := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro a
  apply Metric.continuousAt_iff'.mpr
  intro ε hε
  have hc : Continuous (fun b ↦
      2 - 2 * ∑ v ∈ (f a).weights.support, min ((f a).weights v) ((f b).weights v)) := by
    exact continuous_const.sub (continuous_const.mul
      (continuous_finsetSum _ (fun v _ ↦ continuous_const.min (hf v))))
  have hs : (∑ v ∈ (f a).weights.support,
      min ((f a).weights v) ((f a).weights v)) = 1 := by
    simp only [min_self]
    exact (f a).weights_total
  have he : ∀ᶠ b in 𝓝 a,
      2 - 2 * ∑ v ∈ (f a).weights.support, min ((f a).weights v) ((f b).weights v) < ε :=
    hc.continuousAt.eventually_lt continuousAt_const (by rw [hs]; linarith)
  filter_upwards [he] with b hb
  have hd := twice_commonMass_add_dist (f a) (f b)
  rw [commonMass_eq_sum_left] at hd
  rw [dist_comm]
  linarith

/-- The exact coordinate criterion applies to the already-defined L1 topology. -/
theorem continuous_iff_coordinates {A : Type v} [TopologicalSpace A]
    (f : A → MetricOrderComplex P) :
    Continuous f ↔ ∀ v, Continuous (fun a ↦ (f a).weights v) :=
  ⟨fun h v ↦ (continuous_coordinate v).comp h, continuous_of_coordinates f⟩

/-- Pairs with positive common mass, with the original metric-subspace topology. -/
abbrev OverlappingPairs (P : Type u) [PartialOrder P] :=
  {z : MetricOrderComplex P × MetricOrderComplex P // 0 < commonMass z.1 z.2}

/-- Normalization is continuous in L1, including when its finite support changes. -/
@[fun_prop]
theorem continuous_commonPoint :
    Continuous (fun z : OverlappingPairs P ↦ commonPoint z.1.1 z.1.2 z.2) := by
  apply continuous_of_coordinates
  intro v
  simp only [commonPoint_weights]
  exact (((continuous_coordinate v).comp (continuous_fst.comp continuous_subtype_val)).min
    ((continuous_coordinate v).comp (continuous_snd.comp continuous_subtype_val))).div
      (continuous_commonMass.comp continuous_subtype_val) (fun z ↦ ne_of_gt z.2)

/-- The actual continuous normalized common-point map on the overlap domain. -/
def commonPointMap : C(OverlappingPairs P, MetricOrderComplex P) :=
  ⟨fun z ↦ commonPoint z.1.1 z.1.2 z.2, continuous_commonPoint⟩

end Topology.MetricOrderComplex
