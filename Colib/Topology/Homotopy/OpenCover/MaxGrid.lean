/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Homotopy.OpenCover.IntervalSquare
public import Colib.Topology.Homotopy.OpenCover.Subdivision

/-!
# Max Grid

Actual closed-interval image containment follows from the range of the
corresponding affine subpath, including degenerate intervals.
-/

@[expose] public section

noncomputable section
open Set CategoryTheory
universe u v
namespace FundamentalGroupoid.OpenCover
variable {X : Type u} [TopologicalSpace X] {ι : Type v} {U : ι → Set X}

/-- Actual closed-interval image containment follows from the range of the
corresponding affine subpath, including degenerate intervals. -/
theorem intervalImage_contained {x y : X} (p : Path x y) (i : ι)
    (l r : unitInterval) (hlr : l ≤ r) (hp : Set.range (p.subpath l r) ⊆ U i)
    (t : Set.Icc (l : ℝ) (r : ℝ)) : p (intervalToUnit l r t) ∈ U i := by
  apply hp
  rw [Path.range_subpath_of_le p l r hlr]
  exact ⟨intervalToUnit l r t, ⟨t.property.1, t.property.2⟩, rfl⟩

/-- A cell of the max-grid of two monotone subdivisions has an actual
chart-contained filling. Choose the original segment whose right endpoint is
larger; the entire max-cell parameter interval lies in that original segment. -/
def maxSubpathSquareFilling {x y : X} (p : Path x y)
    (a b c e : unitInterval) (hab : a ≤ b) (hce : c ≤ e)
    (i j : ι) (hp : Set.range (p.subpath a b) ⊆ U i)
    (hq : Set.range (p.subpath c e) ⊆ U j) :
    SquareFilling (U := U)
      (p.subpath (max a c) (max a e)) (p.subpath (max a c) (max b c))
      (p.subpath (max a e) (max b e)) (p.subpath (max b c) (max b e)) := by
  by_cases hbe : b ≤ e
  · exact subpathSquareFilling p j c e
      ⟨max a c, le_max_right _ _, max_le (hab.trans hbe) hce⟩
      ⟨max a e, hce.trans (le_max_right _ _), max_le (hab.trans hbe) le_rfl⟩
      ⟨max b c, le_max_right _ _, max_le hbe hce⟩
      ⟨max b e, hce.trans (le_max_right _ _), max_le hbe le_rfl⟩
      (intervalImage_contained p j c e hce hq)
  · have heb : e ≤ b := le_of_not_ge hbe
    exact subpathSquareFilling p i a b
      ⟨max a c, le_max_left _ _, max_le hab (hce.trans heb)⟩
      ⟨max a e, le_max_left _ _, max_le hab heb⟩
      ⟨max b c, hab.trans (le_max_left _ _), max_le le_rfl (hce.trans heb)⟩
      ⟨max b e, hab.trans (le_max_left _ _), max_le le_rfl heb⟩
      (intervalImage_contained p i a b hab hp)

/-- Two independent actual subdivisions supply every local geometric filling
of their max-grid, without common-refinement choices or a global decoder. -/
def PathSubdivision.maxGridFilling {x y : X} {p : Path x y}
    (s t : PathSubdivision (U := U) p) (i : Fin s.n) (j : Fin t.n) :
    SquareFilling (U := U)
      (p.subpath (max (s.times i.castSucc) (t.times j.castSucc))
        (max (s.times i.castSucc) (t.times j.succ)))
      (p.subpath (max (s.times i.castSucc) (t.times j.castSucc))
        (max (s.times i.succ) (t.times j.castSucc)))
      (p.subpath (max (s.times i.castSucc) (t.times j.succ))
        (max (s.times i.succ) (t.times j.succ)))
      (p.subpath (max (s.times i.succ) (t.times j.castSucc))
        (max (s.times i.succ) (t.times j.succ))) :=
  maxSubpathSquareFilling p _ _ _ _ (s.monotone (Fin.castSucc_le_succ i))
    (t.monotone (Fin.castSucc_le_succ j)) (s.chart i) (t.chart j)
    (s.contained i) (t.contained j)

end FundamentalGroupoid.OpenCover
