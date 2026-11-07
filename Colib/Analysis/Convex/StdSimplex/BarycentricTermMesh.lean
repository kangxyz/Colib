/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Analysis.Convex.StdSimplex.BarycentricMesh
public import Colib.Analysis.Convex.StdSimplex.BarycentricList
public import Colib.Algebra.Homology.OrientedList.SubdivisionTerms

/-!
Adapted from `Quillen/Topology/LocalCoefficients/BarycentricTermMesh.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original maps and signs.

# Mesh contraction on the actual support of recursive subdivision

Every descending face-center term of recursive coning shares the last retained
original vertex with positive uniform mass. This proves contraction directly
for the lists in the constructed chain operator, with no unproved identification
between descending and ascending flag conventions.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open FreeAbelianGroup.OrientedList
open scoped BigOperators Topology

namespace Convexity.StdSimplex.BarycentricSubdivision

/-- A vertex appearing in a tuple contributes its full reciprocal-cardinality
mass to that coordinate of the tuple barycenter. -/
theorem tupleBarycenter_weight_ge_of_vertex {I J : Type*} [Fintype I] [Nonempty I]
    [Fintype J] (v : I → StdSimplex ℝ J) (i : I) (j : J)
    (hi : v i = StdSimplex.single j) :
    (Fintype.card I : ℝ)⁻¹ ≤ (tupleBarycenter v).weights j := by
  rw [tupleBarycenter_weights]
  have hsum : 1 ≤ ∑ k, (v k).weights j := by
    have h := Finset.single_le_sum (fun k _ ↦ (v k).weights_nonneg j)
      (Finset.mem_univ i)
    rw [hi] at h
    simpa only [StdSimplex.weights_single, Finsupp.single_eq_same] using h
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hsum
    (inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card I)))

/-- An original vertex in a nonempty list contributes at least one divided
by the list length to its actual uniform barycenter. Repetitions are allowed. -/
theorem listBarycenter_weight_ge_of_mem {J : Type*} [Fintype J] [Nonempty J]
    (l : List (StdSimplex ℝ J)) (j : J) (hj : StdSimplex.single j ∈ l) :
    (l.length : ℝ)⁻¹ ≤ (listBarycenter l).weights j := by
  cases l with
  | nil => simp at hj
  | cons p l =>
    let v : Fin (l.length + 1) → StdSimplex ℝ J :=
      Fin.cons p (fun k : Fin l.length ↦ l[k.val])
    obtain ⟨i, hi⟩ : ∃ i : Fin (l.length + 1), v i = StdSimplex.single j := by
      rcases List.mem_cons.mp hj with h | h
      · refine ⟨0, ?_⟩
        change p = StdSimplex.single j
        exact h.symm
      · obtain ⟨k, hk, hval⟩ := List.mem_iff_getElem.mp h
        refine ⟨(⟨k, hk⟩ : Fin l.length).succ, ?_⟩
        change l[k] = StdSimplex.single j
        exact hval
    simpa only [listBarycenter, List.length_cons, Fintype.card_fin, v] using
      tupleBarycenter_weight_ge_of_vertex
        v i j hi

/-- Every actual recursive term from a nonempty list of standard vertices has
a common retained vertex, with uniform mass at least the inverse input length. -/
theorem subdivisionTerm_common_coordinate {J : Type*} [Fintype J] [Nonempty J]
    {l k : List (StdSimplex ℝ J)} (hterm : SubdivisionTerm listBarycenter l k)
    (hl : l ≠ []) (hpure : ∀ p ∈ l, ∃ j, p = StdSimplex.single j) :
    ∃ j, StdSimplex.single j ∈ l ∧
      ∀ p ∈ k, (l.length : ℝ)⁻¹ ≤ p.weights j := by
  revert hl hpure
  induction hterm with
  | nil => simp
  | cons l hl i k hk ih =>
    intro _ hpure
    by_cases he : l.eraseIdx i.val = []
    · have hkempty : k = [] := by
        apply List.length_eq_zero_iff.mp
        simpa only [he, List.length_nil] using hk.length
      obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil l hl
      obtain ⟨j, rfl⟩ := hpure p hp
      refine ⟨j, hp, ?_⟩
      intro q hq
      have hq' : q = listBarycenter l := by simpa [hkempty] using hq
      rw [hq']
      exact listBarycenter_weight_ge_of_mem l j hp
    · obtain ⟨j, hj, hweights⟩ := ih he (fun p hp ↦
        hpure p ((List.eraseIdx_sublist l i.val).subset hp))
      have hj' : StdSimplex.single j ∈ l := (List.eraseIdx_sublist l i.val).subset hj
      refine ⟨j, hj', ?_⟩
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact listBarycenter_weight_ge_of_mem l j hj'
      · refine le_trans ?_ (hweights p hp)
        apply inv_anti₀
        · exact_mod_cast List.length_pos_iff.mpr he
        · exact_mod_cast List.length_eraseIdx_le l i.val

/-- The actual original standard-vertex list. -/
def standardVertices (n : ℕ) : List (StdSimplex ℝ (Fin (n + 1))) :=
  List.ofFn StdSimplex.single

/-- The common-coordinate certificate holds for every actual subdivision term
of the original simplex, including either flag orientation convention. -/
theorem standard_subdivisionTerm_common_coordinate {n : ℕ}
    {k : List (StdSimplex ℝ (Fin (n + 1)))}
    (hk : SubdivisionTerm listBarycenter (standardVertices n) k) :
    ∃ j : Fin (n + 1), ∀ p ∈ k, ((n + 1 : ℕ) : ℝ)⁻¹ ≤ p.weights j := by
  obtain ⟨j, _, hj⟩ := subdivisionTerm_common_coordinate hk
    (by simp [standardVertices]) (by
      intro p hp
      obtain ⟨j, hj⟩ := List.mem_ofFn.mp hp
      exact ⟨j, hj.symm⟩)
  exact ⟨j, by simpa [standardVertices] using hj⟩

/-- The exact terms of the recursive chain operator satisfy the same uniform
contraction estimate, in any ordering of their vertices. -/
theorem l1Dist_subdivisionTerm_le {n : ℕ} {I : Type*} [Fintype I]
    {k : List (StdSimplex ℝ (Fin (n + 1)))}
    (hk : SubdivisionTerm listBarycenter (standardVertices n) k)
    (v : I → StdSimplex ℝ (Fin (n + 1))) (hv : ∀ i, v i ∈ k)
    (x y : StdSimplex ℝ I) :
    l1Dist (affineSimplex v x) (affineSimplex v y) ≤ contractionFactor n * l1Dist x y := by
  obtain ⟨j, hj⟩ := standard_subdivisionTerm_common_coordinate hk
  exact l1Dist_affineSimplex_le v j _ (fun i ↦ hj (v i) (hv i)) x y

/-- The simplex lists occurring in actual recursive subdivision, with the
checked recursive support witness retained. -/
abbrev SubdivisionSimplex (n : ℕ) :=
  {l : List (StdSimplex ℝ (Fin (n + 1))) //
    SubdivisionTerm listBarycenter (standardVertices n) l}

/-- The continuous affine simplex associated to an actual recursive term. -/
def subdivisionTermMap {n : ℕ} (t : SubdivisionSimplex n) :
    C(StdSimplex ℝ (Fin (n + 1)), StdSimplex ℝ (Fin (n + 1))) :=
  affineSimplex fun i : Fin (n + 1) ↦ t.val[i.val]'(by
    have h := t.property.length
    simp only [standardVertices, List.length_ofFn] at h
    omega)

/-- Every actual recursive term map has the uniform barycentric contraction. -/
theorem l1Dist_subdivisionTermMap_le {n : ℕ} (t : SubdivisionSimplex n)
    (x y : StdSimplex ℝ (Fin (n + 1))) :
    l1Dist (subdivisionTermMap t x) (subdivisionTermMap t y) ≤
      contractionFactor n * l1Dist x y := by
  apply l1Dist_subdivisionTerm_le t.property
  intro i
  exact List.getElem_mem _

/-- An arbitrary sequence of actual recursive subdivision simplex maps. -/
def iteratedTermMap {n : ℕ} : List (SubdivisionSimplex n) →
    C(StdSimplex ℝ (Fin (n + 1)), StdSimplex ℝ (Fin (n + 1)))
  | [] => ContinuousMap.id _
  | p :: ps => (subdivisionTermMap p).comp (iteratedTermMap ps)

/-- The contraction multiplies at each stage, uniformly in all flag choices. -/
theorem l1Dist_iteratedTermMap_le {n : ℕ}
    (ps : List (SubdivisionSimplex n))
    (x y : StdSimplex ℝ (Fin (n + 1))) :
    l1Dist (iteratedTermMap ps x) (iteratedTermMap ps y) ≤
      contractionFactor n ^ ps.length * l1Dist x y := by
  induction ps with
  | nil => simp [iteratedTermMap]
  | cons p ps ih =>
    calc
      l1Dist (iteratedTermMap (p :: ps) x) (iteratedTermMap (p :: ps) y) ≤
          contractionFactor n *
            l1Dist (iteratedTermMap ps x) (iteratedTermMap ps y) :=
        l1Dist_subdivisionTermMap_le p (iteratedTermMap ps x) (iteratedTermMap ps y)
      _ ≤ contractionFactor n * (contractionFactor n ^ ps.length * l1Dist x y) :=
        mul_le_mul_of_nonneg_left ih (contractionFactor_nonneg n)
      _ = contractionFactor n ^ (p :: ps).length * l1Dist x y := by
        simp only [List.length_cons, pow_succ]
        ring

/-- Uniform mesh decay, starting from the L1 diameter-two standard simplex. -/
theorem l1Dist_iteratedTermMap_le_mesh {n : ℕ}
    (ps : List (SubdivisionSimplex n))
    (x y : StdSimplex ℝ (Fin (n + 1))) :
    l1Dist (iteratedTermMap ps x) (iteratedTermMap ps y) ≤
      2 * contractionFactor n ^ ps.length := by
  calc
    _ ≤ contractionFactor n ^ ps.length * l1Dist x y :=
      l1Dist_iteratedTermMap_le ps x y
    _ ≤ contractionFactor n ^ ps.length * 2 :=
      mul_le_mul_of_nonneg_left (l1Dist_le_two x y)
        (pow_nonneg (contractionFactor_nonneg n) _)
    _ = _ := mul_comm _ _

/-- Every open cover becomes small after a single uniform finite number of
actual barycentric subdivisions of a continuous singular simplex. The depth
works for every sequence of recursive terms. -/
theorem exists_eventually_iteratedTermMap_cover_small {X ι : Type*} [TopologicalSpace X]
    {n : ℕ} (σ : C(StdSimplex ℝ (Fin (n + 1)), X)) (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i) :
    ∃ k : ℕ, ∀ ps : List (SubdivisionSimplex n), k ≤ ps.length →
      ∃ i, Set.range (σ.comp (iteratedTermMap ps)) ⊆ U i := by
  let := coordinateMetric (Fin (n + 1))
  have hpre : ∀ i, IsOpen (σ ⁻¹' U i) := fun i ↦ (hU i).preimage σ.continuous
  have hprecover : ⋃ i, σ ⁻¹' U i = Set.univ := by
    ext x
    simpa using hcover (σ x)
  obtain ⟨ε, hε, hLeb⟩ := CompactSpace.lebesgue_number_lemma
    (fun i ↦ σ ⁻¹' U i) hpre hprecover
  have hlim : Filter.Tendsto (fun k : ℕ ↦ 2 * contractionFactor n ^ k)
      Filter.atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (contractionFactor_nonneg n) (contractionFactor_lt_one n)).const_mul 2
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.mp (hlim.eventually (gt_mem_nhds hε))
  refine ⟨k, fun ps hps ↦ ?_⟩
  have hdiam : Metric.diam (Set.range (iteratedTermMap ps)) ≤ ε := by
    apply Metric.diam_le_of_forall_dist_le hε.le
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact (coordinateDist_le_l1Dist _ _).trans
      ((l1Dist_iteratedTermMap_le_mesh ps x y).trans (hk ps.length hps).le)
  obtain ⟨i, hi⟩ := hLeb (Set.range (iteratedTermMap ps))
    (Set.range_nonempty _) hdiam
  exact ⟨i, fun _ ⟨x, hx⟩ ↦ hx ▸ hi (Set.mem_range_self x)⟩

/-- A single depth at which every actual recursive term is cover-small. -/
theorem exists_iteratedTermMap_cover_small {X ι : Type*} [TopologicalSpace X]
    {n : ℕ} (σ : C(StdSimplex ℝ (Fin (n + 1)), X)) (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i) :
    ∃ k : ℕ, ∀ ps : List (SubdivisionSimplex n), ps.length = k →
      ∃ i, Set.range (σ.comp (iteratedTermMap ps)) ⊆ U i := by
  obtain ⟨k, hk⟩ := exists_eventually_iteratedTermMap_cover_small σ U hU hcover
  exact ⟨k, fun ps hps ↦ hk ps hps.symm.le⟩

/-- A finite family of genuine singular simplices has one common subdivision
depth, valid also at every greater depth. This is the finite-support geometric
input for arbitrary finite singular chains. -/
theorem exists_uniform_iteratedTermMap_cover_small {X ι κ : Type*}
    [TopologicalSpace X] [Finite κ] {n : ℕ}
    (σ : κ → C(StdSimplex ℝ (Fin (n + 1)), X)) (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i) :
    ∃ k : ℕ, ∀ a : κ, ∀ ps : List (SubdivisionSimplex n), k ≤ ps.length →
      ∃ i, Set.range ((σ a).comp (iteratedTermMap ps)) ⊆ U i := by
  classical
  let := Fintype.ofFinite κ
  choose d hd using fun a ↦ exists_eventually_iteratedTermMap_cover_small (σ a) U hU hcover
  refine ⟨Finset.univ.sup d, fun a ps hps ↦ hd a ps (le_trans ?_ hps)⟩
  exact Finset.le_sup (Finset.mem_univ a)

end Convexity.StdSimplex.BarycentricSubdivision
