/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Homotopy.OpenCover.TransitionData
public import Colib.Topology.Homotopy.OpenCover.LocalTrivializations

/-!
# Chart Recovery

The constructed global descent functor recovers every original chart functor
by a natural isomorphism on ALL actual chart paths, with its specified object transports.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set CategoryTheory
universe u v w z
namespace FundamentalGroupoid.OpenCover.TransitionData
variable {X : Type u} [TopologicalSpace X] {ι : Type v} {U : ι → Set X}
    {C : Type w} [Category.{z} C]

/-- The constructed global descent functor recovers every original chart functor
by a natural isomorphism on ALL actual chart paths, with its specified object transports. -/
def descentChartIso (d : TransitionData (C := C) U) (c : CoverData U) (i : ι) :
    FundamentalGroupoid.map ((ContinuousMap.subtypeVal (U i))) ⋙ d.descent c ≅ d.chart i :=
  NatIso.ofComponents (fun x => (d.chartData c).transport i x.as) (by
    intro x y f
    induction f using _root_.Quotient.ind with | _ p =>
      let p0 := p.map ((ContinuousMap.subtypeVal (U i))).continuous
      have hp : range p0 ⊆ U i := by
        rintro _ ⟨t, rfl⟩
        exact (p t).property
      have h := (d.chartData c).descent_local c (d.chartData_compatible c) p0 i hp
      have hl : (Path.inSubset (x := ⟨_, hp (p0).source_mem_range⟩) (y := ⟨_, hp
          (p0).target_mem_range⟩) p0 hp) = p := by
        apply Path.ext
        funext t
        rfl
      change (d.descent c).map (Path.Homotopic.Quotient.mk p0) =
        ((d.chartData c).transport i x.as).hom ≫
          (d.chart i).map (Path.Homotopic.Quotient.mk ((Path.inSubset (x := ⟨_, hp
              (p0).source_mem_range⟩) (y := ⟨_, hp (p0).target_mem_range⟩) p0 hp))) ≫
        ((d.chartData c).transport i y.as).inv at h
      rw [hl] at h
      change (d.descent c).map (Path.Homotopic.Quotient.mk p0) ≫
          ((d.chartData c).transport i y.as).hom =
        ((d.chartData c).transport i x.as).hom ≫
          (d.chart i).map (Path.Homotopic.Quotient.mk p)
      rw [h]
      simp [Category.assoc])

/-- Exact component formula of chart recovery. -/
theorem descentChartIso_hom_app (d : TransitionData (C := C) U) (c : CoverData U)
    (i : ι) (x : U i) :
    (d.descentChartIso c i).hom.app (FundamentalGroupoid.mk x) =
      ((d.chartData c).transport i x).hom := rfl

end FundamentalGroupoid.OpenCover.TransitionData
