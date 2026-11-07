/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.CubicalSubdivision.FaceContainment
public import Mathlib.Data.Finset.Image

/-! # Finite incident-chart constraints for genuine cubical faces

A face carries every chart assigned to a coface which contains it. Thus
lower-dimensional fillings are constrained in all charts needed by later
cells, and interior intersections transfer those constraints exactly.


Implementation provenance:
`Quillen/Topology/CubicalSubdivision/IncidentCharts.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
open scoped Topology unitInterval
namespace Topology.CubicalSubdivision
universe u v

/-- The finite set of charts of all actual cofaces of `F`. -/
def incidentCharts {n m : ℕ} {J : Type u} [DecidableEq J]
    (chart : FaceIndex n m → J) (F : FaceIndex n m) : Finset J := by
  classical
  exact (Finset.univ.filter (fun G ↦ faceSet F ⊆ faceSet G)).image chart

theorem mem_incidentCharts_iff {n m : ℕ} {J : Type u} [DecidableEq J]
    (chart : FaceIndex n m → J) (F : FaceIndex n m) (j : J) :
    j ∈ incidentCharts chart F ↔ ∃ G : FaceIndex n m,faceSet F ⊆ faceSet G ∧ chart G = j := by
  classical
  simp only [incidentCharts,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]

/-- The assigned chart of the face itself is always one of its constraints. -/
theorem self_mem_incidentCharts {n m : ℕ} {J : Type u} [DecidableEq J]
    (chart : FaceIndex n m → J) (F : FaceIndex n m) :
    chart F ∈ incidentCharts chart F :=
  (mem_incidentCharts_iff chart F (chart F)).2 ⟨F,(fun _ hx ↦ hx),rfl⟩

theorem incidentCharts_nonempty {n m : ℕ} {J : Type u} [DecidableEq J]
    (chart : FaceIndex n m → J) (F : FaceIndex n m) :
    (incidentCharts chart F).Nonempty := ⟨chart F,self_mem_incidentCharts chart F⟩

/-- Lower faces retain every constraint of every containing face. -/
theorem incidentCharts_antitone {n m : ℕ} {J : Type u} [DecidableEq J]
    (chart : FaceIndex n m → J) {F G : FaceIndex n m} (hFG : faceSet F ⊆ faceSet G) :
    incidentCharts chart G ⊆ incidentCharts chart F := by
  intro j hj
  obtain ⟨H,hH,hj⟩ := (mem_incidentCharts_iff chart G j).1 hj
  exact (mem_incidentCharts_iff chart F j).2 ⟨H,hFG.trans hH,hj⟩

/-- At an interior intersection, the intersecting face's chart was already
included among the filler constraints. -/
theorem chart_mem_incidentCharts_of_interior {n m : ℕ} {J : Type u} [DecidableEq J]
    (chart : FaceIndex n m → J) (F G : FaceIndex n m)
    (s : Active F → unitInterval) (hs : s ∉ _root_.Cube.boundary (Active F))
    (hx : face F s ∈ faceSet G) : chart G ∈ incidentCharts chart F := by
  obtain ⟨t,ht⟩ := hx
  exact (mem_incidentCharts_iff chart F (chart G)).2
    ⟨G,faceSet_subset_of_interior F G s t hs ht.symm,rfl⟩

/-- Any prescribed family of source-chart subsets gives the exact combined
constraint for a face. No openness of these source sets is required. -/
def incidentChartSet {n m : ℕ} {J : Type u} [DecidableEq J] {E : Type v}
    (chart : FaceIndex n m → J) (R : J → Set E) (F : FaceIndex n m) : Set E :=
  {e | ∀ j ∈ incidentCharts chart F,e ∈ R j}

/-- The combined constraint is monotone under actual face containment. -/
theorem incidentChartSet_mono {n m : ℕ} {J : Type u} [DecidableEq J] {E : Type v}
    (chart : FaceIndex n m → J) (R : J → Set E) {F G : FaceIndex n m}
    (hFG : faceSet F ⊆ faceSet G) : incidentChartSet chart R F ⊆ incidentChartSet chart R G := by
  intro e he j hj
  exact he j (incidentCharts_antitone chart hFG hj)

end Topology.CubicalSubdivision
