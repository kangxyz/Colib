/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.CubicalSubdivision.Cover
public import Mathlib.Topology.CompactOpen

/-!
# Open whole-path pools and one uniform finite time subdivision

The parameter locus on which an entire closed time slab remains in an open
chart is genuinely open, using the compact-open topology on actual paths.
A single finite grid controls every slab for an actual compact cube family.
The chart may depend on the slab and the parameter; the time mesh does not.
No compactness or lifting property of the open parameter loci is asserted.


Implementation provenance:
`Quillen/Topology/PathSubdivision/SlabCover.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

open Topology.CubicalSubdivision


noncomputable section
open Topology TopCat
open scoped Topology unitInterval
universe u v w
namespace Topology.PathSubdivision
open CubicalSubdivision
variable {D : Type u} {B : Type v} [TopologicalSpace D] [TopologicalSpace B]

/-- The literal pool of paths lying in a chart at every time, including both endpoints. -/
def pathSet (U : Set B) : Set C(unitInterval,B) := {γ | ∀ t,γ t ∈ U}

/-- Whole-path containment in an open chart is open in the actual compact-open topology. -/
theorem pathSet_isOpen {U : Set B} (hU : IsOpen U) : IsOpen (pathSet U) := by
  simpa only [pathSet, Set.range_subset_iff] using
    (ContinuousMap.isOpen_setOfPred_range_subset (X := unitInterval) hU)

/-- An intersection of whole-path pools is exactly the pool for the intersection chart. -/
theorem pathSet_inter (U V : Set B) : pathSet (U ∩ V) = pathSet U ∩ pathSet V := by
  ext γ
  exact ⟨fun h ↦ ⟨fun t ↦ (h t).1,fun t ↦ (h t).2⟩,
    fun h t ↦ ⟨h.1 t,h.2 t⟩⟩

/-- The actual affine time slab of the original family, retaining its parameter. -/
def slabMap (H : C(unitInterval × D, B)) (m : ℕ) (i : Fin (m + 1)) :
    C(D,C(unitInterval,B)) where
  toFun d := ⟨fun t ↦ H (intervalCell m i t,d),by fun_prop⟩
  continuous_toFun := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : D × unitInterval ↦ H (intervalCell m i z.2,z.1))
    fun_prop

@[simp] theorem slabMap_apply (H : C(unitInterval × D, B)) (m : ℕ)
    (i : Fin (m + 1)) (d : D) (t : unitInterval) :
    slabMap H m i d t = H (intervalCell m i t,d) := rfl

/-- Original parameters whose entire closed affine time slab lies in the chart. -/
def slabSet (H : C(unitInterval × D, B)) (U : Set B) (m : ℕ) (i : Fin (m + 1)) : Set D :=
  slabMap H m i ⁻¹' pathSet U

theorem mem_slabSet_iff (H : C(unitInterval × D, B)) (U : Set B)
    (m : ℕ) (i : Fin (m + 1)) (d : D) :
    d ∈ slabSet H U m i ↔ ∀ t,H (intervalCell m i t,d) ∈ U := Iff.rfl

/-- Openness uses only the compact time interval; the parameter space may be arbitrary. -/
theorem slabSet_isOpen (H : C(unitInterval × D, B)) {U : Set B}
    (hU : IsOpen U) (m : ℕ) (i : Fin (m + 1)) : IsOpen (slabSet H U m i) :=
  (pathSet_isOpen hU).preimage (slabMap H m i).continuous

theorem slabSet_inter (H : C(unitInterval × D, B)) (U V : Set B)
    (m : ℕ) (i : Fin (m + 1)) :
    slabSet H (U ∩ V) m i = slabSet H U m i ∩ slabSet H V m i := by
  simp only [slabSet,pathSet_inter,Set.preimage_inter]

/-- Adjacent slabs meet at exactly the same original time and family value. -/
theorem slabMap_shared_endpoint (H : C(unitInterval × D, B)) (m : ℕ)
    (i j : Fin (m + 1)) (hij : (i : ℕ) + 1 = j) (d : D) :
    slabMap H m i d 1 = slabMap H m j d 0 :=
  congrArg (fun t ↦ H (t,d)) (intervalCell_shared_face m i j hij)

/-- The first slab starts at the original time zero. -/
theorem intervalCell_first_zero (m : ℕ) : intervalCell m ⟨0,Nat.zero_lt_succ m⟩ 0 = 0 := by
  apply Subtype.ext
  simp [intervalCell]

/-- The last slab ends at the original time one. -/
theorem intervalCell_last_one (m : ℕ) : intervalCell m ⟨m,Nat.lt_succ_self m⟩ 1 = 1 := by
  apply Subtype.ext
  change ((m : ℝ) + 1) / (m+1) = 1
  exact div_self (by positivity)

/-- Every constant original track stays literally constant on every slab.
In particular this applies pointwise to the full prescribed outer boundary. -/
theorem slabMap_of_constant (H : C(unitInterval × D, B)) (d : D) (b : B)
    (h : ∀ t, H (t, d) = b) (m : ℕ) (i : Fin (m + 1)) :
    slabMap H m i d = ContinuousMap.const unitInterval b := by
  ext t
  exact h (intervalCell m i t)

/-- Full constant-track boundary values retain every chart containing that value. -/
theorem mem_slabSet_of_constant (H : C(unitInterval × D, B)) (d : D) (b : B)
    (h : ∀ t, H (t, d) = b) {U : Set B} (hb : b ∈ U) (m : ℕ) (i : Fin (m + 1)) :
    d ∈ slabSet H U m i := by
  intro t
  change H (intervalCell m i t,d) ∈ U
  rw [h]
  exact hb

/-- One finite time mesh works simultaneously for every original cube parameter.
Every closed slab at that parameter lies entirely in one original open chart.
The proof uses the actual product-cube grid, including dimension-zero parameters. -/
theorem exists_uniform_slab_cover (n : ℕ) (H : C(unitInterval × Cube n, B))
    {J : Type w} (U : J → Set B) (hU : ∀ j, IsOpen (U j))
    (hcover : ∀ t d, ∃ j, H (t, d) ∈ U j) :
    ∃ m : ℕ,∀ (i : Fin (m+1)) (d : Cube n),∃ j,d ∈ slabSet H (U j) m i := by
  let F : C(Cube (n+1),B) := ⟨fun z ↦ H (z 0,fun k ↦ z k.succ),by fun_prop⟩
  obtain ⟨m,hm⟩ := exists_grid_map_subordinate (n+1) F U hU
    (fun z ↦ hcover (z 0) (fun k ↦ z k.succ))
  refine ⟨m,fun i d ↦ ?_⟩
  obtain ⟨k,s,hs⟩ := cell_covers n m d
  obtain ⟨j,hj⟩ := hm (Fin.cons i k)
  refine ⟨j,fun t ↦ ?_⟩
  have h := hj (Fin.cons t s)
  change H (intervalCell m i t,cell n m k s) ∈ U j at h
  change H (intervalCell m i t,d) ∈ U j
  simpa only [hs] using h

/-- The two whole-slab parameter opens cover the actual cube for every step
of one fixed finite time subdivision. Neither open locus is assumed compact. -/
theorem exists_uniform_two_slab_cover (n : ℕ) (H : C(unitInterval × Cube n, B))
    (U V : Set B) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : ∀ t d, H (t, d) ∈ U ∪ V) :
    ∃ m : ℕ,∀ i : Fin (m+1),slabSet H U m i ∪ slabSet H V m i = Set.univ := by
  let W : Bool → Set B := fun b ↦ if b then V else U
  have hW : ∀ b,IsOpen (W b) := by intro b; cases b <;> assumption
  have hc : ∀ t d,∃ b,H (t,d) ∈ W b := by
    intro t d
    rcases hcover t d with h | h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  obtain ⟨m,hm⟩ := exists_uniform_slab_cover n H W hW hc
  refine ⟨m,fun i ↦ Set.eq_univ_of_forall (fun d ↦ ?_)⟩
  obtain ⟨b,hb⟩ := hm i d
  cases b
  · exact Or.inl hb
  · exact Or.inr hb

end Topology.PathSubdivision
