/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Homotopy.OpenCover.OverlapLoops
public import Colib.Topology.Homotopy.OpenCover.Descent

/-!
# Transition Data

Local functors and coherent actual overlap-path transitions. These are
local data, not a globally defined decoder or a faithfulness assumption.
-/

@[expose] public section

noncomputable section
open Set CategoryTheory
universe u v w z
namespace FundamentalGroupoid.OpenCover
variable {X : Type u} [TopologicalSpace X] {ι : Type v}
variable {C : Type w} [Category.{z} C]

/-- Local functors and coherent actual overlap-path transitions. These are
local data, not a globally defined decoder or a faithfulness assumption. -/
structure TransitionData (U : ι → Set X) where
  /-- The local functor for each chart. -/
  chart : ∀ i, FundamentalGroupoid (U i) ⥤ C
  /-- Object identifications on each actual overlap. -/
  transition : ∀ i j x (hi : x ∈ U i) (hj : x ∈ U j),
    (chart i).obj (FundamentalGroupoid.mk ⟨x, hi⟩) ≅
      (chart j).obj (FundamentalGroupoid.mk ⟨x, hj⟩)
  cocycle : ∀ i j k x (hi : x ∈ U i) (hj : x ∈ U j) (hk : x ∈ U k),
    transition i j x hi hj ≪≫ transition j k x hj hk = transition i k x hi hk
  naturality : ∀ i j {x y : X} (p : Path x y)
    (hi : Set.range p ⊆ U i) (hj : Set.range p ⊆ U j),
    (chart i).map (Path.Homotopic.Quotient.mk ((Path.inSubset (x := ⟨_, hi
        (p).source_mem_range⟩) (y := ⟨_, hi (p).target_mem_range⟩) p hi))) ≫
      (transition i j y (hi p.target_mem_range) (hj p.target_mem_range)).hom =
    (transition i j x (hi p.source_mem_range) (hj p.source_mem_range)).hom ≫
      (chart j).map (Path.Homotopic.Quotient.mk ((Path.inSubset (x := ⟨_, hj
          (p).source_mem_range⟩) (y := ⟨_, hj (p).target_mem_range⟩) p hj)))

namespace TransitionData
variable {U : ι → Set X} (d : TransitionData (C := C) U) (c : CoverData U)

/-- Choose one chart containing a specified ambient point. -/
def chosenChart (x : X) : ι := Classical.choose (Set.mem_iUnion.mp (c.covers x))
theorem mem_chosenChart (x : X) : x ∈ U (chosenChart c x) :=
  Classical.choose_spec (Set.mem_iUnion.mp (c.covers x))

/-- Choose a chart at each actual point and use its object; transition isos
provide the exact transport to every other applicable chart. -/
def chartData : ChartData (C := C) U where
  obj x := (d.chart (chosenChart c x)).obj (FundamentalGroupoid.mk ⟨x, mem_chosenChart c x⟩)
  chart := d.chart
  transport i x := d.transition (chosenChart c x.val) i x.val (mem_chosenChart c x.val) x.property

/-- Coherence and actual overlap naturality prove normalized compatibility. -/
theorem chartData_compatible : (d.chartData c).Compatible := by
  intro i j x y p hi hj
  let ax := d.transition (chosenChart c x) i x (mem_chosenChart c x) (hi p.source_mem_range)
  let ay := d.transition (chosenChart c y) i y (mem_chosenChart c y) (hi p.target_mem_range)
  let bx := d.transition (chosenChart c x) j x (mem_chosenChart c x) (hj p.source_mem_range)
  let byy := d.transition (chosenChart c y) j y (mem_chosenChart c y) (hj p.target_mem_range)
  let tx := d.transition i j x (hi p.source_mem_range) (hj p.source_mem_range)
  let ty := d.transition i j y (hi p.target_mem_range) (hj p.target_mem_range)
  let f := (d.chart i).map (Path.Homotopic.Quotient.mk ((Path.inSubset (x := ⟨_, hi
      (p).source_mem_range⟩) (y := ⟨_, hi (p).target_mem_range⟩) p hi)))
  let g := (d.chart j).map (Path.Homotopic.Quotient.mk ((Path.inSubset (x := ⟨_, hj
      (p).source_mem_range⟩) (y := ⟨_, hj (p).target_mem_range⟩) p hj)))
  have hx : ax ≪≫ tx = bx := d.cocycle _ _ _ _ _ _ _
  have hy : ay ≪≫ ty = byy := d.cocycle _ _ _ _ _ _ _
  have hn : f ≫ ty.hom = tx.hom ≫ g := d.naturality i j p hi hj
  change ax.hom ≫ f ≫ ay.inv = bx.hom ≫ g ≫ byy.inv
  calc
    ax.hom ≫ f ≫ ay.inv = (ax.hom ≫ f ≫ ty.hom) ≫ byy.inv := by
      rw [← hy]
      simp
    _ = (ax.hom ≫ tx.hom ≫ g) ≫ byy.inv := by rw [hn]
    _ = bx.hom ≫ g ≫ byy.inv := by
      rw [← hx]
      simp

/-- Global descent constructed solely from the specified local transition data. -/
def descent : FundamentalGroupoid X ⥤ C :=
  (d.chartData c).descent c (d.chartData_compatible c)

end TransitionData
end FundamentalGroupoid.OpenCover
