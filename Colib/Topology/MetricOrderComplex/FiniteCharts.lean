/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.MetricOrderComplex.RealizationReconstruction
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Reconstruction on one fixed finite chain

A strict finite-chain coordinate chart is a compact-to-Hausdorff embedding.
Its inverse on its metric range is continuous, and the exact reconstruction
formula gives a continuous map from this one range to the original weak
realization. Degenerate charts have the same range as their nondegenerate
reduction. No global continuity of the unmodified reconstruction is asserted.
-/

/-! Implementation source: `Quillen/Topology/MetricOrderComplex/FiniteCharts.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Charts use the pinned native finite simplex. -/
@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory SSet Opposite
open scoped Simplicial Topology

universe u v

namespace Topology.MetricOrderComplex

variable {P : Type u} [PartialOrder P]

/-- A metric point lies in a chart exactly when its support is in the chart's vertex range. -/
theorem mem_range_simplexCoordinates {n : SimplexCategory} (s : (nerve P).obj (op n))
    (x : MetricOrderComplex P) :
    x ∈ Set.range (simplexCoordinates s) ↔
      (x.weights.support : Set P) ⊆ Set.range s.obj := by
  classical
  constructor
  · rintro ⟨t, rfl⟩
    exact simplexCoordinates_support_subset s t
  · intro hx
    let S := x.weights.support
    let f : S → Fin (n.len + 1) := fun p ↦ Classical.choose (hx p.property)
    have hf : ∀ p : S, s.obj (f p) = p.val := fun p ↦ Classical.choose_spec (hx p.property)
    let w : _root_.stdSimplex ℝ S :=
      ⟨fun p ↦ x.weights p, fun p ↦ x.weights_nonneg p, by
        calc
          _ = ∑ p ∈ S, x.weights p := Finset.sum_coe_sort S (fun p ↦ x.weights p)
          _ = 1 := by
            change x.weights.sum (fun _ a ↦ a) = 1
            exact x.weights_total⟩
    refine ⟨_root_.stdSimplex.map f w, ?_⟩
    apply ext
    intro p
    rw [simplexCoordinates_weights, sum_single_stdSimplex_map]
    simp_rw [hf]
    change (∑ q : S, Finsupp.single q.val (x.weights q.val)) p = x.weights p
    have hsum : (∑ q : S, Finsupp.single q.val (x.weights q.val)) = x.weights := by
      calc
        _ = ∑ q ∈ S, Finsupp.single q (x.weights q) :=
          Finset.sum_coe_sort S (fun q ↦ Finsupp.single q (x.weights q))
        _ = x.weights := by
          change x.weights.sum (fun q a ↦ Finsupp.single q a) = x.weights
          exact Finsupp.sum_single x.weights
    exact congrArg (fun z : P →₀ ℝ ↦ z p) hsum

/-- A strict finite-chain chart is an embedding for the actual L1 metric topology. -/
theorem simplexCoordinates_isClosedEmbedding {n : SimplexCategory}
    (s : (nerve P).obj (op n)) (hs : StrictMono s.obj) :
    Topology.IsClosedEmbedding (simplexCoordinates s) :=
  (simplexCoordinates s).continuous.isClosedEmbedding
    (simplexCoordinates_injective s hs.injective)

/-- The ordinary finite simplex is homeomorphic to its metric chart range. -/
def simplexCoordinatesRangeHomeomorph {n : SimplexCategory}
    (s : (nerve P).obj (op n)) (hs : StrictMono s.obj) :
    _root_.stdSimplex ℝ (Fin (n.len + 1)) ≃ₜ Set.range (simplexCoordinates s) :=
  (simplexCoordinates_isClosedEmbedding s hs).isEmbedding.toHomeomorph

/-- Reconstruction is continuous on a fixed strict chart range. -/
theorem continuous_reconstruction_strict_range {n : SimplexCategory}
    (s : (nerve P).obj (op n)) (hs : StrictMono s.obj) :
    Continuous (fun x : Set.range (simplexCoordinates s) ↦ realizationReconstruction x.1) := by
  let e := simplexCoordinatesRangeHomeomorph s hs
  have hc := (realizationSimplex s).continuous.comp e.symm.continuous
  convert hc using 1
  funext x
  rcases x with ⟨x, ⟨t, rfl⟩⟩
  simp only [Function.comp_apply, realizationReconstruction_simplex, e,
    simplexCoordinatesRangeHomeomorph, Topology.IsEmbedding.toHomeomorph_symm_apply]

/-- Repeated vertices do not change continuity on the one fixed finite chart range. -/
theorem continuous_reconstruction_range {n : SimplexCategory} (s : (nerve P).obj (op n)) :
    Continuous (fun x : Set.range (simplexCoordinates s) ↦ realizationReconstruction x.1) := by
  obtain ⟨m, a, ha, ⟨q, hq⟩, hs⟩ := (nerve P).exists_nonDegenerate s
  have hr : Set.range s.obj = Set.range q.obj := by
    rw [hs]
    change Set.range (fun i ↦ q.obj (a i)) = Set.range q.obj
    ext p
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨a i, rfl⟩
    · rintro ⟨j, rfl⟩
      obtain ⟨i, hi⟩ := (SimplexCategory.epi_iff_surjective.mp ha) j
      exact ⟨i, congrArg q.obj hi⟩
  have he : Set.range (simplexCoordinates s) = Set.range (simplexCoordinates q) := by
    ext x
    rw [mem_range_simplexCoordinates, mem_range_simplexCoordinates, hr]
  rw [he]
  exact continuous_reconstruction_strict_range q
    ((PartialOrder.mem_nerve_nonDegenerate_iff_strictMono q).mp hq)

/-- Any continuous family supported in one fixed chain reconstructs continuously. -/
theorem continuous_reconstruction_of_support_subset {A : Type v} [TopologicalSpace A]
    {n : SimplexCategory} (s : (nerve P).obj (op n)) (f : C(A, MetricOrderComplex P))
    (hf : ∀ a, ((f a).weights.support : Set P) ⊆ Set.range s.obj) :
    Continuous (fun a ↦ realizationReconstruction (f a)) := by
  let g : A → Set.range (simplexCoordinates s) := fun a ↦
    ⟨f a, (mem_range_simplexCoordinates s (f a)).mpr (hf a)⟩
  have hg : Continuous g := by fun_prop
  exact (continuous_reconstruction_range s).comp hg

end Topology.MetricOrderComplex
