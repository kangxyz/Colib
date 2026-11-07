/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.Cube.RadialExpansion
public import Mathlib.Data.Finset.Card

/-!
# Actual thin-support normalization of a cube map

For a coordinate band `(a,b)` and `p ≤ d`, the thin region consists of cube points with at least
`p` coordinates in that band. If the original inverse image of an arbitrary target subset already
lies in this region on the boundary, the explicit boundary-fixed radial expansion normalizes the
whole inverse image. No separation, regularity, connectivity, or closedness hypothesis is imposed
on the target or subset. Empty coordinate sets and the endpoint values `p=0` and `p=d` are included.
This is the single-cell deformation input for Puppe's coordinate-counting proof of excision.
-/

/-! Implementation provenance: adapted from
`Quillen/Topology/Cube/ThinSupport.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, finite bounds,
whole path families and universe parameters are retained in their native owners. -/
@[expose] public section

noncomputable section
open Topology

open scoped Topology unitInterval

universe u

namespace Cube

variable {d : ℕ}

/-- The actual original coordinates lying strictly inside the chosen band. -/
def bandCoordinates (a b : unitInterval) (x : Fin d → unitInterval) : Finset (Fin d) := by
  classical
  exact Finset.univ.filter (fun i ↦ a < x i ∧ x i < b)

/-- The support region in which at least the displayed number of original coordinates lie in
one chosen open band. -/
def thinSupport (a b : unitInterval) (p : ℕ) : Set (Fin d → unitInterval) :=
  {x | p ≤ (bandCoordinates a b x).card}

/-- The zeroth thin region is the whole original cube. -/
@[simp] theorem thinSupport_zero (a b : unitInterval) : thinSupport (d := d) a b 0 = Set.univ := by
  ext x
  simp [thinSupport]

/-- A larger required coordinate count defines a smaller original support region. -/
theorem thinSupport_antitone (a b : unitInterval) {p q : ℕ} (hpq : p ≤ q) :
    thinSupport (d := d) a b q ⊆ thinSupport a b p :=
  fun _ hx ↦ hpq.trans hx

/-- The midpoint of the actual supplied band, which need not be centered in the unit interval. -/
def bandCenter (a b : unitInterval) : unitInterval :=
  ⟨((a : ℝ) + b) / 2, by constructor <;> linarith [a.property.1, a.property.2,
    b.property.1, b.property.2]⟩

/-- A positive lower cap for the radial denominator, retaining the actual band's width. -/
def bandRadius (a b : unitInterval) (hab : a < b) : unitInterval :=
  ⟨((b : ℝ) - a) / 2, by
    change (a : ℝ) < b at hab
    constructor <;> linarith [a.property.1, b.property.2]⟩

theorem bandCenter_pos (a b : unitInterval) (hab : a < b) : 0 < (bandCenter a b : ℝ) := by
  change (a : ℝ) < b at hab
  change 0 < ((a : ℝ) + b) / 2
  linarith [a.property.1]

theorem bandCenter_lt_one (a b : unitInterval) (hab : a < b) : (bandCenter a b : ℝ) < 1 := by
  change (a : ℝ) < b at hab
  change ((a : ℝ) + b) / 2 < 1
  linarith [b.property.2]

theorem bandRadius_pos (a b : unitInterval) (hab : a < b) : 0 < (bandRadius a b hab : ℝ) := by
  change (a : ℝ) < b at hab
  change 0 < ((b : ℝ) - a) / 2
  linarith

/-- The original explicit expansion associated to the supplied band. -/
def bandExpansion (a b : unitInterval) (hab : a < b) :
    C((Fin d → unitInterval), Fin d → unitInterval) :=
  radialExpansion (bandCenter a b) (bandRadius a b hab) (bandCenter_pos a b hab)
    (bandCenter_lt_one a b hab) (bandRadius_pos a b hab)

/-- The actual original homotopy is fixed pointwise on the whole cube boundary. -/
def bandExpansionHomotopy (a b : unitInterval) (hab : a < b) :
    (ContinuousMap.id (Fin d → unitInterval)).HomotopyRel (bandExpansion a b hab)
      (_root_.Cube.boundary (Fin d)) :=
  radialExpansionHomotopy (bandCenter a b) (bandRadius a b hab) (bandCenter_pos a b hab)
    (bandCenter_lt_one a b hab) (bandRadius_pos a b hab)

/-- Expansion cannot create a new original coordinate inside the band. -/
theorem bandCoordinates_expansion_subset (a b : unitInterval) (hab : a < b)
    (x : Fin d → unitInterval) :
    bandCoordinates a b (bandExpansion a b hab x) ⊆ bandCoordinates a b x := by
  classical
  intro i hi
  simp only [bandCoordinates, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact radialExpansion_mem_band_imp a b (bandCenter a b) (bandRadius a b hab)
    (by change (a : ℝ) < b at hab; change (a : ℝ) < ((a : ℝ) + b) / 2; linarith)
    (by change (a : ℝ) < b at hab; change ((a : ℝ) + b) / 2 < b; linarith)
    (bandCenter_pos a b hab) (bandCenter_lt_one a b hab) (bandRadius_pos a b hab) x i hi

/-- If even one original coordinate lies outside the band, the expansion reaches the actual
cube boundary. This is a statement about the explicit map, not a chosen deformation. -/
theorem bandExpansion_mem_boundary_of_not_all (a b : unitInterval) (hab : a < b)
    (x : Fin d → unitInterval) (hx : ¬ ∀ i, a < x i ∧ x i < b) :
    bandExpansion a b hab x ∈ _root_.Cube.boundary (Fin d) := by
  apply radialExpansion_mem_boundary
  push Not at hx
  obtain ⟨i, hi⟩ := hx
  have hg := coordinateGauge_le_radialGauge (bandCenter a b) x i
  have hc₀ := bandCenter_pos a b hab
  have hc₁ := bandCenter_lt_one a b hab
  have hr := bandRadius_pos a b hab
  have hc_le := (bandCenter a b).property.2
  have hc_nonneg := (bandCenter a b).property.1
  by_cases hia : a < x i
  · have hib : b ≤ x i := hi hia
    have he : (bandRadius a b hab : ℝ) ≤
        ((x i : ℝ) - bandCenter a b) / (1 - bandCenter a b) := by
      apply (le_div_iff₀ (sub_pos.mpr hc₁)).mpr
      have hm := mul_nonneg (le_of_lt hr) hc_nonneg
      change (bandRadius a b hab : ℝ) * (1 - bandCenter a b) ≤ (x i : ℝ) - bandCenter a b
      change (b : ℝ) ≤ x i at hib
      dsimp only [bandRadius, bandCenter] at *
      nlinarith
    exact he.trans ((le_max_right _ _).trans hg)
  · have hia' : x i ≤ a := le_of_not_gt hia
    have he : (bandRadius a b hab : ℝ) ≤
        ((bandCenter a b : ℝ) - x i) / bandCenter a b := by
      apply (le_div_iff₀ hc₀).mpr
      have hm := mul_nonneg (le_of_lt hr) (sub_nonneg.mpr hc_le)
      change (x i : ℝ) ≤ a at hia'
      dsimp only [bandRadius, bandCenter] at *
      nlinarith
    exact he.trans ((le_max_left _ _).trans hg)

/-- The explicit original expansion achieves the single-cell thin-support normalization.
Every original boundary value is preserved by `bandExpansionHomotopy`. -/
theorem preimage_subset_thinSupport (a b : unitInterval) (hab : a < b) (p : ℕ) (hp : p ≤ d)
    {Y : Type u} [TopologicalSpace Y] (f : C((Fin d → unitInterval), Y)) (A : Set Y)
    (hboundary : ∀ x ∈ _root_.Cube.boundary (Fin d), f x ∈ A → x ∈ thinSupport a b p) :
    (f.comp (bandExpansion a b hab)) ⁻¹' A ⊆ thinSupport a b p := by
  classical
  intro x hx
  by_cases hall : ∀ i, a < x i ∧ x i < b
  · have he : bandCoordinates a b x = Finset.univ := by
      ext i
      simp only [bandCoordinates, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun _ ↦ trivial, fun _ ↦ hall i⟩
    change p ≤ (bandCoordinates a b x).card
    simpa only [he, Finset.card_univ, Fintype.card_fin] using hp
  · have ht := hboundary (bandExpansion a b hab x)
      (bandExpansion_mem_boundary_of_not_all a b hab x hall) hx
    exact ht.trans (Finset.card_le_card (bandCoordinates_expansion_subset a b hab x))

/-- The normalized map is joined to the original map by the actual boundary-fixed homotopy. -/
theorem exists_homotopyRel_preimage_subset_thinSupport
    (a b : unitInterval) (hab : a < b) (p : ℕ) (hp : p ≤ d)
    {Y : Type u} [TopologicalSpace Y] (f : C((Fin d → unitInterval), Y)) (A : Set Y)
    (hboundary : ∀ x ∈ _root_.Cube.boundary (Fin d), f x ∈ A → x ∈ thinSupport a b p) :
    ∃ g : C((Fin d → unitInterval), Y),
      Nonempty (f.HomotopyRel g (_root_.Cube.boundary (Fin d))) ∧
        g ⁻¹' A ⊆ thinSupport a b p :=
  ⟨f.comp (bandExpansion a b hab), ⟨(bandExpansionHomotopy a b hab).compContinuousMap f⟩,
    preimage_subset_thinSupport a b hab p hp f A hboundary⟩

/-- Disjoint coordinate bands cannot simultaneously contain more coordinates than the actual
cube dimension. This includes zero-dimensional cubes and zero required counts. -/
theorem thinSupport_disjoint (a b c e : unitInterval) (hbc : b ≤ c) (p q : ℕ)
    (hpq : d < p + q) : Disjoint (thinSupport (d := d) a b p) (thinSupport c e q) := by
  classical
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hd : Disjoint (bandCoordinates a b x) (bandCoordinates c e x) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    simp only [bandCoordinates, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    exact (not_lt_of_ge (hi.2.le.trans hbc)) hj.1
  have hc := Finset.card_le_card
    (show bandCoordinates a b x ∪ bandCoordinates c e x ⊆ Finset.univ from
      Finset.subset_univ _)
  rw [Finset.card_union_of_disjoint hd, Finset.card_univ, Fintype.card_fin] at hc
  exact (Nat.not_lt_of_ge ((Nat.add_le_add hx hy).trans hc)) hpq

end Cube
