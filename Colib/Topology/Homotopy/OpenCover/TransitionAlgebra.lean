/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Homotopy.OpenCover.TransitionData

/-!
# Transition Algebra

Adjacent normalized chart transports cancel to the specified actual transition.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set CategoryTheory
universe u v w z
namespace FundamentalGroupoid.OpenCover.TransitionData
variable {X : Type u} [TopologicalSpace X] {ι : Type v} {U : ι → Set X}
variable {C : Type w} [Category.{z} C]
variable (d : TransitionData (C := C) U) (c : CoverData U)

/-- Adjacent normalized chart transports cancel to the specified actual transition. -/
@[reassoc]
theorem transport_change (i j : ι) (x : X) (hi : x ∈ U i) (hj : x ∈ U j) :
    ((d.chartData c).transport i ⟨x, hi⟩).inv ≫
      ((d.chartData c).transport j ⟨x, hj⟩).hom = (d.transition i j x hi hj).hom := by
  have h := d.cocycle (chosenChart c x) i j x (mem_chosenChart c x) hi hj
  change (d.transition (chosenChart c x) i x _ hi).inv ≫
    (d.transition (chosenChart c x) j x _ hj).hom = _
  rw [← h]
  simp

/-- The reverse cancellation is the inverse of exactly the same transition. -/
@[reassoc]
theorem transport_change_inv (i j : ι) (x : X) (hi : x ∈ U i) (hj : x ∈ U j) :
    ((d.chartData c).transport j ⟨x, hj⟩).inv ≫
      ((d.chartData c).transport i ⟨x, hi⟩).hom = (d.transition i j x hi hj).inv := by
  have h := d.cocycle (chosenChart c x) i j x (mem_chosenChart c x) hi hj
  change (d.transition (chosenChart c x) j x _ hj).inv ≫
    (d.transition (chosenChart c x) i x _ hi).hom = _
  rw [← h]
  simp

/-- The three-part actual path formula, retaining the two exact transition
arrows and the original endpoint object transports. -/
theorem pathValue_three {a b e f : X} (p : Path a b) (q : Path b e) (r : Path e f)
    (i j k : ι) (hp : range p ⊆ U i) (hq : range q ⊆ U j) (hr : range r ⊆ U k) :
    (d.chartData c).pathValue c (p.trans (q.trans r)) =
      ((d.chartData c).transport i ⟨a, hp p.source_mem_range⟩).hom ≫
      (d.chart i).map (Path.Homotopic.Quotient.mk ((Path.inSubset (x := ⟨_, hp
          (p).source_mem_range⟩) (y := ⟨_, hp (p).target_mem_range⟩) p hp))) ≫
      (d.transition i j b (hp p.target_mem_range) (hq q.source_mem_range)).hom ≫
      (d.chart j).map (Path.Homotopic.Quotient.mk ((Path.inSubset (x := ⟨_, hq
          (q).source_mem_range⟩) (y := ⟨_, hq (q).target_mem_range⟩) q hq))) ≫
      (d.transition j k e (hq q.target_mem_range) (hr r.source_mem_range)).hom ≫
      (d.chart k).map (Path.Homotopic.Quotient.mk ((Path.inSubset (x := ⟨_, hr
          (r).source_mem_range⟩) (y := ⟨_, hr (r).target_mem_range⟩) r hr))) ≫
      ((d.chartData c).transport k ⟨f, hr r.target_mem_range⟩).inv := by
  have hc := d.chartData_compatible c
  rw [(d.chartData c).pathValue_trans c hc, (d.chartData c).pathValue_trans c hc,
    (d.chartData c).pathValue_local c hc i p hp,
    (d.chartData c).pathValue_local c hc j q hq,
    (d.chartData c).pathValue_local c hc k r hr]
  simp only [ChartData.localValue, Category.assoc, transport_change_assoc]
  rfl

end FundamentalGroupoid.OpenCover.TransitionData
