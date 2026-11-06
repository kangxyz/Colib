/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyLifting.Basic
public import Mathlib.Topology.Compactness.Compact

/-! # Continuous variable-time traversal at stationary parameters

The time selector may be discontinuous where a whole compact parameter family
is constant. The tube lemma proves continuity there, with no separation
assumption on the target. This justifies accelerating a stationary homotopy
through a continuously shrinking time interval.


Implementation provenance:
`Quillen/Topology/HomotopyLifting/VariableTime.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
open scoped Topology unitInterval
namespace Topology
universe u v w z

/-- At a parameter where a compact family is constant, arbitrary changes of
its compact coordinate remain continuous. -/
theorem continuousAt_compact_eval_of_constant
    {K : Type u} {X : Type v} {Y : Type w} {Z : Type z}
    [TopologicalSpace K] [CompactSpace K] [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z]
    (H : C(K × X, Y)) (a : Z → K) (b : C(Z, X)) (z₀ : Z) (k₀ : K)
    (hH : ∀ k, H (k, b z₀) = H (k₀, b z₀)) :
    ContinuousAt (fun z ↦ H (a z,b z)) z₀ := by
  rw [continuousAt_def]
  intro S hS
  obtain ⟨U,hUS,hU,h₀⟩ := mem_nhds_iff.mp hS
  have hprod : (Set.univ : Set K) ×ˢ {b z₀} ⊆ H ⁻¹' U := by
    rintro ⟨k,x⟩ ⟨_,hx⟩
    have hx' : x = b z₀ := hx
    subst x
    change H (k,b z₀) ∈ U
    rw [hH k,← hH (a z₀)]
    exact h₀
  obtain ⟨V,W,_,hW,hV,hz,hVW⟩ := generalized_tube_lemma isCompact_univ
    isCompact_singleton (hU.preimage H.continuous) hprod
  have hn : b ⁻¹' W ∈ nhds z₀ :=
    (hW.preimage b.continuous).mem_nhds (hz (Set.mem_singleton (b z₀)))
  exact Filter.mem_of_superset hn (fun z hz ↦ hUS (hVW ⟨hV (Set.mem_univ _),hz⟩))

/-- Traverse the unit interval within a duration, then stop at its endpoint.
At duration zero the value is zero; only stationary homotopies use that case. -/
def acceleratedTime (t duration : unitInterval) : unitInterval :=
  ⟨min ((t : ℝ)/(duration : ℝ)) 1,
    le_min (div_nonneg t.2.1 duration.2.1) zero_le_one, min_le_right _ _⟩

@[simp] theorem acceleratedTime_zero (duration : unitInterval) : acceleratedTime 0 duration = 0
    := by
  apply Subtype.ext
  simp [acceleratedTime]

@[simp] theorem acceleratedTime_mul (t duration : unitInterval) (hd : duration ≠ 0) :
    acceleratedTime (t * duration) duration = t := by
  have hd' : (duration : ℝ) ≠ 0 := unitInterval.coe_ne_zero.mpr hd
  apply Subtype.ext
  change min (((t : ℝ)*(duration : ℝ))/(duration : ℝ)) 1 = (t : ℝ)
  rw [mul_div_cancel_right₀ _ hd',min_eq_left t.2.2]

/-- Away from zero duration the ordinary quotient formula is continuous. -/
theorem continuousAt_acceleratedTime {t d : unitInterval} (hd : d ≠ 0) :
    ContinuousAt (fun z : unitInterval × unitInterval ↦ acceleratedTime z.1 z.2) (t,d) := by
  have hd' : (d : ℝ) ≠ 0 := unitInterval.coe_ne_zero.mpr hd
  apply tendsto_subtype_rng.mpr
  change ContinuousAt (fun z : unitInterval × unitInterval ↦ min ((z.1 : ℝ)/(z.2 : ℝ)) 1) (t,d)
  have hn : ContinuousAt (fun z : unitInterval × unitInterval ↦ (z.1 : ℝ)) (t,d) := by fun_prop
  have hd : ContinuousAt (fun z : unitInterval × unitInterval ↦ (z.2 : ℝ)) (t,d) := by fun_prop
  exact (hn.div hd hd').min continuousAt_const

/-- The actual accelerated homotopy is continuous, including at vanishing
duration. Constancy there is a geometric input, not an inverse-family choice. -/
def acceleratedHomotopy {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (H : C(unitInterval × X, Y)) (duration : C(X, unitInterval))
    (hH : ∀ x, duration x = 0 → ∀ t, H (t, x) = H (0, x)) :
    C(unitInterval × X,Y) where
  toFun z := H (acceleratedTime z.1 (duration z.2),z.2)
  continuous_toFun := by
    rw [continuous_iff_continuousAt]
    intro z
    by_cases hz : duration z.2 = 0
    · exact continuousAt_compact_eval_of_constant H
        (fun z ↦ acceleratedTime z.1 (duration z.2)) ContinuousMap.snd z 0
        (hH z.2 hz)
    · have hd : ContinuousAt (fun z : unitInterval × X ↦ (z.1,duration z.2)) z := by fun_prop
      have ht := (continuousAt_acceleratedTime (t := z.1) hz).comp_of_eq hd rfl
      exact H.continuous.continuousAt.comp (ht.prodMk continuousAt_snd)

@[simp] theorem acceleratedHomotopy_zero {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (H : C(unitInterval × X, Y)) (duration : C(X, unitInterval))
    (hH : ∀ x, duration x = 0 → ∀ t, H (t, x) = H (0, x)) (x : X) :
    acceleratedHomotopy H duration hH (0,x) = H (0,x) := by
  change H (acceleratedTime 0 (duration x),x) = _
  rw [acceleratedTime_zero]

/-- Evaluating at the actual scaled time recovers the original homotopy. -/
@[simp] theorem acceleratedHomotopy_mul {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (H : C(unitInterval × X, Y)) (duration : C(X, unitInterval))
    (hH : ∀ x, duration x = 0 → ∀ t, H (t, x) = H (0, x)) (t : unitInterval) (x : X) :
    acceleratedHomotopy H duration hH (t * duration x,x) = H (t,x) := by
  change H (acceleratedTime (t * duration x) (duration x),x) = _
  by_cases hx : duration x = 0
  · rw [hx,mul_zero,acceleratedTime_zero]
    exact (hH x hx t).symm
  · rw [acceleratedTime_mul t (duration x) hx]

end Topology
