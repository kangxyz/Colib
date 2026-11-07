/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.MetricOrderComplex.Coordinates
public import Mathlib.Geometry.Convex.ConvexSpace.Topology
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Algebra.Ring.Real

/-!
# Finite-chain charts in the metric order complex

A chain of vertices sends barycentric weights to their pushforward, adding
weights at repeated vertices. On each finite chain this map is continuous
for the actual L1 metric. These charts respect every simplex operator,
including faces with zero weights and degeneracies with repeated vertices.
-/

/-! Implementation source: `Quillen/Topology/MetricOrderComplex/SimplexCoordinates.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Finite realization charts use the pinned
native finite-support simplex, with its actual coordinate pushforward. -/
@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Convexity Opposite
open scoped Simplicial Topology

universe u v w

namespace Topology.MetricOrderComplex

variable {P : Type u} [PartialOrder P]

/-- Classical equality is used only for finite supports. -/
local instance : DecidableEq P := Classical.decEq P

/-- Coordinatewise continuity suffices on one fixed finite support. -/
theorem continuous_of_support_subset {A : Type v} [TopologicalSpace A]
    (f : A → MetricOrderComplex P) (s : Finset P)
    (hs : ∀ a, (f a).weights.support ⊆ s)
    (hf : ∀ v, Continuous (fun a ↦ (f a).weights v)) : Continuous f := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro a
  apply Metric.continuousAt_iff'.mpr
  intro ε hε
  have hc : Continuous (fun b ↦ ∑ v ∈ s, dist ((f b).weights v) ((f a).weights v)) := by
    exact continuous_finsetSum _ (fun v _ ↦ (hf v).dist continuous_const)
  have he : ∀ᶠ b in 𝓝 a, ∑ v ∈ s, dist ((f b).weights v) ((f a).weights v) < ε :=
    hc.continuousAt.eventually_lt continuousAt_const (by simpa using hε)
  filter_upwards [he] with b hb
  change coordinateDistance (f b) (f a) < ε
  rwa [coordinateDistance_eq_sum _ _ s (hs b) (hs a)]

/-- Push barycentric coordinates forward along a chain, aggregating repetitions. -/
def chainCoordinates {ι : Type v} (v : ι → P) (hv : IsChain (· ≤ ·) (Set.range v))
    (t : StdSimplex ℝ ι) : MetricOrderComplex P := by
  classical
  refine ⟨t.map v, hv.mono ?_⟩
  intro p hp
  by_contra h
  exact Finsupp.mem_support_iff.mp hp (Finsupp.mapDomain_of_notMem_range t.weights p h)

@[simp]
theorem chainCoordinates_weights {ι : Type v} (v : ι → P)
    (hv : IsChain (· ≤ ·) (Set.range v)) (t : StdSimplex ℝ ι) :
    (chainCoordinates v hv t).weights = t.weights.mapDomain v := rfl

/-- Positive weights have exactly their image support, even when vertices repeat. -/
theorem chainCoordinates_support {ι : Type v} (v : ι → P)
    (hv : IsChain (· ≤ ·) (Set.range v)) (t : StdSimplex ℝ ι) :
    (chainCoordinates v hv t).weights.support = t.weights.support.image v := by
  classical
  apply Finset.Subset.antisymm Finsupp.mapDomain_support
  rintro p hp
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
  apply Finsupp.mem_support_iff.mpr
  have hpos : 0 < t.weights i :=
    lt_of_le_of_ne (t.weights_nonneg i) (Ne.symm (Finsupp.mem_support_iff.mp hi))
  have hle : t.weights i ≤ (t.weights.mapDomain v) (v i) := by
    rw [Finsupp.mapDomain, Finsupp.sum_apply]
    change t.weights i ≤ ∑ j ∈ t.weights.support, (Finsupp.single (v j) (t.weights j)) (v i)
    have hn : ∀ j ∈ t.weights.support, 0 ≤ (Finsupp.single (v j) (t.weights j)) (v i) := by
      intro j _
      simp only [Finsupp.single_apply]
      split_ifs
      · exact t.weights_nonneg j
      · rfl
    simpa using Finset.single_le_sum hn hi
  exact ne_of_gt (hpos.trans_le hle)

/-- An injective chain preserves each of its individual barycentric coordinates. -/
theorem chainCoordinates_weights_apply {ι : Type v} (v : ι → P)
    (hv : IsChain (· ≤ ·) (Set.range v)) (hi : Function.Injective v)
    (t : StdSimplex ℝ ι) (i : ι) :
    (chainCoordinates v hv t).weights (v i) = t.weights i :=
  Finsupp.mapDomain_apply_of_injective hi _ _

@[simp]
theorem chainCoordinates_single {ι : Type v} (v : ι → P)
    (hv : IsChain (· ≤ ·) (Set.range v)) (i : ι) :
    chainCoordinates v hv (StdSimplex.single i) = vertex (v i) := by
  apply Subtype.ext
  exact StdSimplex.map_single i v

/-- Pushforward along a composite is exactly successive aggregation of weights. -/
theorem chainCoordinates_comp {ι : Type v} {κ : Type w} (v : ι → P)
    (hv : IsChain (· ≤ ·) (Set.range v)) (g : κ → ι)
    (hvg : IsChain (· ≤ ·) (Set.range (v ∘ g))) (t : StdSimplex ℝ κ) :
    chainCoordinates v hv (t.map g) = chainCoordinates (v ∘ g) hvg t := by
  apply Subtype.ext
  exact (StdSimplex.map_comp t g v).symm

omit [PartialOrder P] in
/-- A finite sum of vertex weights vanishes outside the vertex range. -/
theorem sum_single_eq_zero_of_notMem_range {ι : Type v} [Fintype ι]
    (v : ι → P) (t : ι → ℝ) {p : P} (hp : p ∉ Set.range v) :
    (∑ i, Finsupp.single (v i) (t i)) p = 0 := by
  classical
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
  apply Finset.sum_eq_zero
  intro i _
  split_ifs with h
  · exact False.elim (hp ⟨i, h⟩)
  · rfl

omit [PartialOrder P] in
/-- Finite pushforward composes with the native simplex map, including repeated vertices. -/
theorem sum_single_stdSimplex_map {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
    (v : κ → P) (f : ι → κ) (t : StdSimplex ℝ ι) :
    (∑ j, Finsupp.single (v j) ((t.map f).weights j)) =
      ∑ i, Finsupp.single (v (f i)) (t.weights i) := by
  calc
    _ = (t.map f).weights.mapDomain v := (Finsupp.mapDomain_fintype _ _).symm
    _ = t.weights.mapDomain (v ∘ f) := by
      rw [StdSimplex.weights_map, ← Finsupp.mapDomain_comp]
    _ = _ := Finsupp.mapDomain_fintype _ _

/-- The metric barycentric chart is the native pushforward along its chain of vertices. -/
def simplexCoordinates {n : SimplexCategory} (s : (nerve P).obj (op n)) :
    C(StdSimplex ℝ (Fin (n.len + 1)), MetricOrderComplex P) where
  toFun := chainCoordinates s.obj s.monotone.isChain_range
  continuous_toFun := by
    classical
    apply continuous_of_support_subset _ (Finset.univ.image s.obj)
    · intro t p hp
      change p ∈ (t.weights.mapDomain s.obj).support at hp
      have hp' : p ∈ t.weights.support.image s.obj := Finsupp.mapDomain_support hp
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp'
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    · intro p
      change Continuous (fun t : StdSimplex ℝ (Fin (n.len + 1)) ↦ (t.map s.obj).weights p)
      exact (StdSimplex.continuous_weights_apply ℝ p).comp
        (StdSimplex.continuous_map (R := ℝ) s.obj)

@[simp]
theorem simplexCoordinates_weights {n : SimplexCategory} (s : (nerve P).obj (op n))
    (t : StdSimplex ℝ (Fin (n.len + 1))) :
    (simplexCoordinates s t).weights = ∑ i, Finsupp.single (s.obj i) (t.weights i) :=
  Finsupp.mapDomain_fintype _ _

/-- A finite chart has no support outside its vertices. -/
theorem simplexCoordinates_support_subset {n : SimplexCategory}
    (s : (nerve P).obj (op n)) (t : StdSimplex ℝ (Fin (n.len + 1))) :
    ((simplexCoordinates s t).weights.support : Set P) ⊆ Set.range s.obj := by
  intro p hp
  by_contra h
  exact Finsupp.mem_support_iff.mp hp (Finsupp.mapDomain_of_notMem_range t.weights p h)

/-- Exact compatibility with every simplex operator, including all degeneracies. -/
theorem simplexCoordinates_naturality {n m : SimplexCategory} (a : n ⟶ m)
    (s : (nerve P).obj (op m)) (t : StdSimplex ℝ (Fin (n.len + 1))) :
    simplexCoordinates s (t.map a) =
      simplexCoordinates ((nerve P).map a.op s) t := by
  apply Subtype.ext
  exact (StdSimplex.map_comp t a s.obj).symm

@[simp]
theorem simplexCoordinates_single {n : SimplexCategory} (s : (nerve P).obj (op n))
    (i : Fin (n.len + 1)) :
    simplexCoordinates s (StdSimplex.single i) = vertex (s.obj i) :=
  chainCoordinates_single s.obj s.monotone.isChain_range i

/-- An injective simplex chart retains each individual native barycentric coordinate. -/
theorem simplexCoordinates_weights_apply {n : SimplexCategory}
    (s : (nerve P).obj (op n)) (hs : Function.Injective s.obj)
    (t : StdSimplex ℝ (Fin (n.len + 1))) (i : Fin (n.len + 1)) :
    (simplexCoordinates s t).weights (s.obj i) = t.weights i :=
  Finsupp.mapDomain_apply_of_injective hs t.weights i

/-- An injective native simplex chart is injective. -/
theorem simplexCoordinates_injective {n : SimplexCategory}
    (s : (nerve P).obj (op n)) (hs : Function.Injective s.obj) :
    Function.Injective (simplexCoordinates s) := by
  intro t q h
  apply StdSimplex.ext
  exact Finsupp.mapDomain_injective hs (congrArg weights h)

end Topology.MetricOrderComplex
