/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Homotopy.OpenCover.Chart
public import Colib.CategoryTheory.ComposableArrows.Grid

/-!
# Chart Homotopy

A homotopy whose entire image is in a subset lifts to that actual subtype.
-/

@[expose] public section

/-! Local homotopies and finite chart-labelled grid descent.
No global decoder, subdivision existence or comparison faithfulness is assumed. -/

noncomputable section
open CategoryTheory Set
universe u v w z

namespace FundamentalGroupoid.OpenCover

variable {X : Type u} [TopologicalSpace X] {ι : Type v}
variable {C : Type w} [Category.{z} C] {U : ι → Set X}

/-- A homotopy whose entire image is in a subset lifts to that actual subtype. -/
def liftPathHomotopy {V : Set X} {x y : X} {p q : Path x y}
    (H : p.Homotopy q) (hp : Set.range p ⊆ V) (hq : Set.range q ⊆ V)
    (hH : ∀ t, H t ∈ V) : ((Path.inSubset (x := ⟨_, hp (p).source_mem_range⟩) (y := ⟨_, hp
        (p).target_mem_range⟩) p hp)).Homotopy ((Path.inSubset (x := ⟨_, hq
        (q).source_mem_range⟩) (y := ⟨_, hq (q).target_mem_range⟩) q hq)) where
  toFun t := ⟨H t, hH t⟩
  continuous_toFun := H.continuous.subtype_mk _
  map_zero_left t := Subtype.ext (H.map_zero_left t)
  map_one_left t := Subtype.ext (H.map_one_left t)
  prop' t s hs := Subtype.ext (H.prop' t s hs)

namespace ChartData

variable (d : ChartData (C := C) U)

set_option backward.isDefEq.respectTransparency false in
/-- Local decoding respects a homotopy inside the actual chart, not merely an
ambient homotopy whose boundary happens to lie in the chart. -/
theorem localValue_homotopy (i : ι) {x y : X} {p q : Path x y}
    (hp : Set.range p ⊆ U i) (hq : Set.range q ⊆ U i)
    (H : p.Homotopy q) (hH : ∀ t, H t ∈ U i) :
    d.localValue i p hp = d.localValue i q hq := by
  have he : Path.Homotopic.Quotient.mk ((Path.inSubset (x := ⟨_, hp (p).source_mem_range⟩) (y :=
      ⟨_, hp (p).target_mem_range⟩) p hp)) =
      Path.Homotopic.Quotient.mk ((Path.inSubset (x := ⟨_, hq (q).source_mem_range⟩) (y := ⟨_,
          hq (q).target_mem_range⟩) q hq)) :=
    Quotient.sound ⟨liftPathHomotopy H hp hq hH⟩
  exact congrArg (fun f : FundamentalGroupoid.mk (⟨x, hp p.source_mem_range⟩ : U i) ⟶
      FundamentalGroupoid.mk (⟨y, hp p.target_mem_range⟩ : U i) =>
    (d.transport i _).hom ≫ (d.chart i).map f ≫ (d.transport i _).inv) he

/-- The four actual chart paths form a commuting square when the two boundary
composites are homotopic through that chart. -/
theorem localValue_square (i : ι) {a b c e : X}
    (p : Path a b) (q : Path a c) (r : Path b e) (s : Path c e)
    (hp : Set.range p ⊆ U i) (hq : Set.range q ⊆ U i)
    (hr : Set.range r ⊆ U i) (hs : Set.range s ⊆ U i)
    (hpr : Set.range (p.trans r) ⊆ U i) (hqs : Set.range (q.trans s) ⊆ U i)
    (H : (p.trans r).Homotopy (q.trans s)) (hH : ∀ t, H t ∈ U i) :
    CommSq (d.localValue i p hp) (d.localValue i q hq)
      (d.localValue i r hr) (d.localValue i s hs) := by
  constructor
  rw [← d.localValue_trans i p r hp hr hpr, ← d.localValue_trans i q s hq hs hqs]
  exact d.localValue_homotopy i hpr hqs H hH

/-- Relabeling each edge by any chart containing the same actual path does not
change its finite ordered value. This includes empty chains. -/
theorem finiteValue_chart_independent (hc : d.Compatible) {n : ℕ}
    (x : Fin (n + 1) → X) (p : ∀ j : Fin n, Path (x j.castSucc) (x j.succ))
    (i k : Fin n → ι) (hi : ∀ j, Set.range (p j) ⊆ U (i j))
    (hk : ∀ j, Set.range (p j) ⊆ U (k j)) :
    finiteChainComp (fun j => d.obj (x j)) (fun j => d.localValue (i j) (p j) (hi j)) =
      finiteChainComp (fun j => d.obj (x j)) (fun j => d.localValue (k j) (p j) (hk j)) := by
  have he : (fun j => d.localValue (i j) (p j) (hi j)) =
      (fun j => d.localValue (k j) (p j) (hk j)) := by
    funext j
    exact hc (i j) (k j) (p j) (hi j) (hk j)
  rw [he]

end ChartData
end FundamentalGroupoid.OpenCover
