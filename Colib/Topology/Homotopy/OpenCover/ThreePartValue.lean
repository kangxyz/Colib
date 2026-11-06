/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Homotopy.OpenCover.ThreeParts
public import Colib.Topology.Homotopy.OpenCover.TransitionAlgebra

/-!
# Three Part Value

The actual unsplit path has the three-chart value, not merely a formally
concatenated surrogate. The endpoint casts are those of the original path.
-/

@[expose] public section

noncomputable section
open Set CategoryTheory
universe u v w z
namespace FundamentalGroupoid.OpenCover.TransitionData
variable {X : Type u} [TopologicalSpace X] {ι : Type v} {U : ι → Set X}
variable {C : Type w} [Category.{z} C]
variable (d : TransitionData (C := C) U) (c : CoverData U)

/-- The actual unsplit path has the three-chart value, not merely a formally
concatenated surrogate. The endpoint casts are those of the original path. -/
theorem pathValue_subpath_three {x y : X} (p : Path x y) (a b : unitInterval)
    (i j k : ι) (hp : range (firstPart p a) ⊆ U i)
    (hq : range (p.subpath a b) ⊆ U j) (hr : range (lastPart p b) ⊆ U k) :
    (d.chartData c).pathValue c p =
      ((d.chartData c).transport i ⟨x, hp (firstPart p a).source_mem_range⟩).hom ≫
      (d.chart i).map (Path.Homotopic.Quotient.mk ((Path.inSubset (x := ⟨_, hp ((firstPart p
          a)).source_mem_range⟩) (y := ⟨_, hp ((firstPart p a)).target_mem_range⟩) (firstPart p
          a) hp))) ≫
      (d.transition i j (p a) (hp (firstPart p a).target_mem_range)
        (hq (p.subpath a b).source_mem_range)).hom ≫
      (d.chart j).map (Path.Homotopic.Quotient.mk ((Path.inSubset (x := ⟨_, hq ((p.subpath a
          b)).source_mem_range⟩) (y := ⟨_, hq ((p.subpath a b)).target_mem_range⟩) (p.subpath a
          b) hq))) ≫
      (d.transition j k (p b) (hq (p.subpath a b).target_mem_range)
        (hr (lastPart p b).source_mem_range)).hom ≫
      (d.chart k).map (Path.Homotopic.Quotient.mk ((Path.inSubset (x := ⟨_, hr ((lastPart p
          b)).source_mem_range⟩) (y := ⟨_, hr ((lastPart p b)).target_mem_range⟩) (lastPart p b)
          hr))) ≫
      ((d.chartData c).transport k ⟨y, hr (lastPart p b).target_mem_range⟩).inv := by
  rw [← (d.chartData c).pathValue_homotopy c (d.chartData_compatible c)
    (threePartHomotopy p a b)]
  exact d.pathValue_three c _ _ _ i j k hp hq hr

end FundamentalGroupoid.OpenCover.TransitionData
