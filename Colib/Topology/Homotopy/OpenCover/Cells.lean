/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Homotopy.OpenCover.ChartHomotopy

/-!
# Cells

Actual cell data. The whole boundary homotopy, not only its four edges,
lies in the chosen chart. No global path evaluator is supplied.
-/

@[expose] public section

noncomputable section
open CategoryTheory Set
universe u v w z
namespace FundamentalGroupoid.OpenCover

variable {X : Type u} [TopologicalSpace X] {ι : Type v}
variable {C : Type w} [Category.{z} C] {U : ι → Set X}

/-- Actual cell data. The whole boundary homotopy, not only its four edges,
lies in the chosen chart. No global path evaluator is supplied. -/
structure SquareFilling {a b c e : X}
    (p : Path a b) (q : Path a c) (r : Path b e) (s : Path c e) where
  /-- A chart containing all four boundary paths and the filling. -/
  chart : ι
  top : Set.range p ⊆ U chart
  left : Set.range q ⊆ U chart
  right : Set.range r ⊆ U chart
  bottom : Set.range s ⊆ U chart
  /-- The actual endpoint-fixed homotopy filling the boundary square. -/
  homotopy : (p.trans r).Homotopy (q.trans s)
  contained : ∀ t, homotopy t ∈ U chart

namespace SquareFilling

variable (d : ChartData (C := C) U) (hc : d.Compatible)
include hc

/-- A cell commutes for any edge-chart choices. Overlap compatibility compares
actual shared edge paths, rather than asserting agreement only at vertices. -/
theorem commSq {a b c e : X}
    {p : Path a b} {q : Path a c} {r : Path b e} {s : Path c e}
    (f : SquareFilling (U := U) p q r s) (ip iq ir is : ι)
    (hp : Set.range p ⊆ U ip) (hq : Set.range q ⊆ U iq)
    (hr : Set.range r ⊆ U ir) (hs : Set.range s ⊆ U is) :
    CommSq (d.localValue ip p hp) (d.localValue iq q hq)
      (d.localValue ir r hr) (d.localValue is s hs) := by
  rw [hc ip f.chart p hp f.top, hc iq f.chart q hq f.left,
    hc ir f.chart r hr f.right, hc is f.chart s hs f.bottom]
  have hpr : Set.range (p.trans r) ⊆ U f.chart := by
    rintro _ ⟨t, rfl⟩
    exact (f.homotopy.map_zero_left t) ▸ f.contained (0, t)
  have hqs : Set.range (q.trans s) ⊆ U f.chart := by
    rintro _ ⟨t, rfl⟩
    exact (f.homotopy.map_one_left t) ▸ f.contained (1, t)
  exact d.localValue_square f.chart p q r s f.top f.left f.right f.bottom
    hpr hqs f.homotopy f.contained

end SquareFilling

namespace ChartData

variable (d : ChartData (C := C) U)

/-- The ordered boundary values of a finite grid commute. Edge charts may be
chosen independently; each cell supplies a chart-contained actual homotopy.
Zero width/height and repeated vertices are allowed, and C need not be a groupoid. -/
theorem finiteGrid_localValue (hc : d.Compatible) {m n : ℕ}
    (x : Fin (m + 1) → Fin (n + 1) → X)
    (h : ∀ i, ∀ j : Fin n, Path (x i j.castSucc) (x i j.succ))
    (v : ∀ i : Fin m, ∀ j, Path (x i.castSucc j) (x i.succ j))
    (ih : Fin (m + 1) → Fin n → ι) (iv : Fin m → Fin (n + 1) → ι)
    (hh : ∀ i j, Set.range (h i j) ⊆ U (ih i j))
    (hv : ∀ i j, Set.range (v i j) ⊆ U (iv i j))
    (fill : ∀ (i : Fin m) (j : Fin n), SquareFilling (U := U)
      (h i.castSucc j) (v i j.castSucc) (v i j.succ) (h i.succ j)) :
    CommSq
      (finiteChainComp (fun j => d.obj (x 0 j))
        (fun j => d.localValue (ih 0 j) (h 0 j) (hh 0 j)))
      (finiteChainComp (fun i => d.obj (x i 0))
        (fun i => d.localValue (iv i 0) (v i 0) (hv i 0)))
      (finiteChainComp (fun i => d.obj (x i (Fin.last n)))
        (fun i => d.localValue (iv i (Fin.last n)) (v i (Fin.last n)) (hv i (Fin.last n))))
      (finiteChainComp (fun j => d.obj (x (Fin.last m) j))
        (fun j => d.localValue (ih (Fin.last m) j) (h (Fin.last m) j) (hh (Fin.last m) j))) := by
  exact finiteGridCommSq (fun i j => d.obj (x i j))
    (fun i j => d.localValue (ih i j) (h i j) (hh i j))
    (fun i j => d.localValue (iv i j) (v i j) (hv i j))
    (fun i j => (fill i j).commSq d hc _ _ _ _ _ _ _ _)

end ChartData
end FundamentalGroupoid.OpenCover
