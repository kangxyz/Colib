/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.UnitInterval
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# A continuous subdivision scale for interval paths

The compact-open path space `C(I, I)` carries its compatible supremum metric.
A bad pair `(γ, r)` admits two times at distance at most `r` whose images
are at distance at least `1 / 12`. These pairs form a closed set: they are
the projection of a closed set with compact fiber `I × I`.

The distance from `(γ, 0)` to that fixed bad set is positive and continuous.
Half this distance, capped at one, is an actual continuously varying
subdivision scale. No local-to-global lifting conclusion is assumed.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/Homotopy/TimeChange.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual maps and hypotheses. -/
@[expose] public section


noncomputable section

open scoped Topology unitInterval
open unitInterval

namespace Topology

/-- Pairs of paths and scales admitting an oscillation of at least `1 / 12`. -/
def pathSubdivisionBad : Set (C(I, I) × ℝ) :=
  {p | ∃ s t : I, dist s t ≤ p.2 ∧ (1 / 12 : ℝ) ≤ dist (p.1 s) (p.1 t)}

/-- The bad-scale set is closed, because both time parameters range over a
compact space. -/
theorem isClosed_pathSubdivisionBad : IsClosed pathSubdivisionBad := by
  let S : Set ((C(I, I) × ℝ) × (I × I)) :=
    {p | dist p.2.1 p.2.2 ≤ p.1.2 ∧
      (1 / 12 : ℝ) ≤ dist (p.1.1 p.2.1) (p.1.1 p.2.2)}
  have hS : IsClosed S := by
    apply IsClosed.inter
    · exact isClosed_le (continuous_snd.fst.dist continuous_snd.snd) continuous_fst.snd
    · exact isClosed_le continuous_const
        ((continuous_eval.comp (continuous_fst.fst.prodMk continuous_snd.fst)).dist
          (continuous_eval.comp (continuous_fst.fst.prodMk continuous_snd.snd)))
  have heq : pathSubdivisionBad = Prod.fst '' S := by
    ext p
    constructor
    · rintro ⟨s, t, hst, hγ⟩
      exact ⟨(p, s, t), ⟨hst, hγ⟩, rfl⟩
    · rintro ⟨⟨q, s, t⟩, h, rfl⟩
      exact ⟨s, t, h⟩
  rw [heq]
  exact isClosedMap_fst_of_compactSpace _ hS

/-- The bad set is nonempty; the identity path at scale one witnesses it. -/
theorem pathSubdivisionBad_nonempty : pathSubdivisionBad.Nonempty := by
  refine ⟨(ContinuousMap.id I, 1), (0 : I), (1 : I), ?_, ?_⟩ <;>
    norm_num [Subtype.dist_eq, Real.dist_eq]

/-- A zero scale is never bad. -/
theorem notMem_pathSubdivisionBad_zero (γ : C(I, I)) :
    (γ, (0 : ℝ)) ∉ pathSubdivisionBad := by
  rintro ⟨s, t, hst, hγ⟩
  have h : s = t := dist_eq_zero.mp (le_antisymm hst dist_nonneg)
  subst t
  norm_num at hγ

/-- An explicit positive continuous subdivision scale on the path space. -/
def pathSubdivisionScale (γ : C(I, I)) : ℝ :=
  min 1 (Metric.infDist (γ, (0 : ℝ)) pathSubdivisionBad / 2)

theorem continuous_pathSubdivisionScale : Continuous pathSubdivisionScale := by
  exact continuous_const.min
    (((Metric.continuous_infDist_pt pathSubdivisionBad).comp
      (continuous_id.prodMk continuous_const)).div_const 2)

theorem pathSubdivisionScale_pos (γ : C(I, I)) : 0 < pathSubdivisionScale γ := by
  apply lt_min (by norm_num)
  apply half_pos
  exact (isClosed_pathSubdivisionBad.notMem_iff_infDist_pos pathSubdivisionBad_nonempty).mp
    (notMem_pathSubdivisionBad_zero γ)

theorem pathSubdivisionScale_le_one (γ : C(I, I)) : pathSubdivisionScale γ ≤ 1 :=
  min_le_left _ _

/-- Closed time steps of length at most the chosen scale have strictly
controlled oscillation. -/
theorem pathSubdivisionScale_controls (γ : C(I, I)) (s t : I)
    (hst : dist s t ≤ pathSubdivisionScale γ) :
    dist (γ s) (γ t) < (1 / 12 : ℝ) := by
  by_contra h
  have hbad : (γ, pathSubdivisionScale γ) ∈ pathSubdivisionBad :=
    ⟨s, t, hst, le_of_not_gt h⟩
  have hle := Metric.infDist_le_dist_of_mem (x := (γ, (0 : ℝ))) hbad
  have hpos := pathSubdivisionScale_pos γ
  have hhalf : pathSubdivisionScale γ ≤
      Metric.infDist (γ, (0 : ℝ)) pathSubdivisionBad / 2 := min_le_right _ _
  simp only [Prod.dist_eq, dist_self, Real.dist_eq, zero_sub, abs_neg,
    abs_of_pos hpos, max_eq_right hpos.le] at hle
  linarith

/-- The scale as a continuous map into the unit interval. -/
def pathSubdivisionScaleMap : C(C(I, I), I) :=
  ⟨fun γ ↦ ⟨pathSubdivisionScale γ,
      (pathSubdivisionScale_pos γ).le, pathSubdivisionScale_le_one γ⟩,
    continuous_pathSubdivisionScale.subtype_mk _⟩

@[simp]
theorem coe_pathSubdivisionScaleMap (γ : C(I, I)) :
    (pathSubdivisionScaleMap γ : ℝ) = pathSubdivisionScale γ := rfl

/-- Real-coordinate formulation of the subdivision estimate. -/
theorem pathSubdivisionScale_controls_abs (γ : C(I, I)) (s t : I)
    (hst : |(s : ℝ) - (t : ℝ)| ≤ pathSubdivisionScale γ) :
    |(γ s : ℝ) - (γ t : ℝ)| < (1 / 12 : ℝ) := by
  have h := pathSubdivisionScale_controls γ s t
    (by simpa only [Subtype.dist_eq, Real.dist_eq] using hst)
  simpa only [Subtype.dist_eq, Real.dist_eq] using h

/-- Every path has an open neighborhood with one common positive subdivision
scale. This is useful when a finite subdivision is fixed locally in a family. -/
theorem exists_pathSubdivision_neighborhood (γ : C(I, I)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ U : Set C(I, I), IsOpen U ∧ γ ∈ U ∧
      ∀ η ∈ U, ∀ s t : I, dist s t ≤ ε → dist (η s) (η t) < (1 / 12 : ℝ) := by
  refine ⟨pathSubdivisionScale γ / 2, half_pos (pathSubdivisionScale_pos γ),
    {η | pathSubdivisionScale γ / 2 < pathSubdivisionScale η},
    isOpen_lt continuous_const continuous_pathSubdivisionScale,
    half_lt_self (pathSubdivisionScale_pos γ), ?_⟩
  intro η hη s t hst
  exact pathSubdivisionScale_controls η s t (hst.trans hη.le)

end Topology
