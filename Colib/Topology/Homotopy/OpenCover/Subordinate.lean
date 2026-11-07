/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Homotopy.OpenCover.Rectangle
public import Colib.Topology.Homotopy.OpenCover.OpenCoverExistence

/-!
# Subordinate

A finite actual homotopy grid, with a chart containing each entire closed cell.
-/

@[expose] public section

noncomputable section
open Set
universe u v
namespace FundamentalGroupoid.OpenCover
variable {X : Type u} [TopologicalSpace X] {ι : Type v} {U : ι → Set X}

/-- A finite actual homotopy grid, with a chart containing each entire closed cell. -/
structure HomotopySubdivision {x y : X} {p q : Path x y} (H : p.Homotopy q) where
  /-- The number of subdivisions in each square coordinate. -/
  n : ℕ
  /-- The common ordered subdivision parameters for both coordinates. -/
  times : Fin (n + 1) → unitInterval
  monotone : Monotone times
  first : times 0 = 0
  last : times (Fin.last n) = 1
  /-- A containing chart for every entire closed grid cell. -/
  chart : Fin n → Fin n → ι
  contained : ∀ j k, H '' (Icc (times j.castSucc) (times j.succ) ×ˢ
    Icc (times k.castSucc) (times k.succ)) ⊆ U (chart j k)

/-- Compactness provides a finite grid; the ambient chart family need not be finite. -/
theorem homotopySubdivision_nonempty {x y : X} {p q : Path x y} (H : p.Homotopy q)
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : Set.range H ⊆ ⋃ i, U i) :
    Nonempty (HomotopySubdivision (U := U) H) := by
  obtain ⟨n, t, h0, h1, hm, h⟩ :=
    ContinuousMap.square_exists_subdivision_openCover H.toContinuousMap U hU hcover
  choose chart hc using h
  exact ⟨⟨n, t, hm, h0, h1, chart, hc⟩⟩

/-- The endpoint requirements exclude an empty grid. -/
theorem HomotopySubdivision.pos {x y : X} {p q : Path x y} {H : p.Homotopy q}
    (g : HomotopySubdivision (U := U) H) : 0 < g.n := by
  by_contra h
  have hn : g.n = 0 := by omega
  have he : (0 : Fin (g.n + 1)) = Fin.last g.n := by apply Fin.ext; simp [hn]
  have h01 : (0 : unitInterval) = 1 := g.first.symm.trans ((congrArg g.times he).trans g.last)
  exact zero_ne_one h01

/-- Every subordinate cell supplies its actual chart-contained boundary homotopy. -/
def HomotopySubdivision.filling {x y : X} {p q : Path x y} {H : p.Homotopy q}
    (g : HomotopySubdivision (U := U) H) (i j : Fin g.n) :
    SquareFilling (U := U)
      ((H.eval (g.times i.castSucc)).subpath (g.times j.castSucc) (g.times j.succ))
      ((homotopyColumn H (g.times j.castSucc)).subpath (g.times i.castSucc) (g.times i.succ))
      ((homotopyColumn H (g.times j.succ)).subpath (g.times i.castSucc) (g.times i.succ))
      ((H.eval (g.times i.succ)).subpath (g.times j.castSucc) (g.times j.succ)) :=
  homotopyRectangleFilling H _ _ _ _ (g.monotone (Fin.castSucc_le_succ i))
    (g.monotone (Fin.castSucc_le_succ j)) (g.chart i j) (g.contained i j)

/-- Every vertex of a nonempty finite interval is incident to an edge. -/
theorem fin_exists_incident {n : ℕ} (hn : 0 < n) (i : Fin (n + 1)) :
    ∃ j : Fin n, i = j.castSucc ∨ i = j.succ := by
  by_cases hi : i.val < n
  · exact ⟨⟨i.val, hi⟩, Or.inl (Fin.ext rfl)⟩
  · refine ⟨⟨n - 1, by omega⟩, Or.inr ?_⟩
    apply Fin.ext
    simp only [Fin.val_succ]
    omega

/-- Horizontal edge charts come from incident whole cells, including boundary edges. -/
theorem HomotopySubdivision.horizontal_chart {x y : X} {p q : Path x y}
    {H : p.Homotopy q} (g : HomotopySubdivision (U := U) H)
    (i : Fin (g.n + 1)) (j : Fin g.n) :
    ∃ k, Set.range ((H.eval (g.times i)).subpath
      (g.times j.castSucc) (g.times j.succ)) ⊆ U k := by
  obtain ⟨r, hr | hr⟩ := fin_exists_incident g.pos i
  · subst i
    exact ⟨(g.filling r j).chart, (g.filling r j).top⟩
  · subst i
    exact ⟨(g.filling r j).chart, (g.filling r j).bottom⟩

/-- Vertical edge charts likewise come from incident whole cells. -/
theorem HomotopySubdivision.vertical_chart {x y : X} {p q : Path x y}
    {H : p.Homotopy q} (g : HomotopySubdivision (U := U) H)
    (i : Fin g.n) (j : Fin (g.n + 1)) :
    ∃ k, Set.range ((homotopyColumn H (g.times j)).subpath
      (g.times i.castSucc) (g.times i.succ)) ⊆ U k := by
  obtain ⟨r, hr | hr⟩ := fin_exists_incident g.pos j
  · subst j
    exact ⟨(g.filling i r).chart, (g.filling i r).left⟩
  · subst j
    exact ⟨(g.filling i r).chart, (g.filling i r).right⟩

end FundamentalGroupoid.OpenCover
