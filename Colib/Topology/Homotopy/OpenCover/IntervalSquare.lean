/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Homotopy.OpenCover.Cells

/-!
# Interval Square

The actual affine path in a real closed interval.
-/

@[expose] public section

noncomputable section
open Set CategoryTheory
universe u v
namespace FundamentalGroupoid.OpenCover

/-- The actual affine path in a real closed interval. -/
def realIntervalPath {l r : ℝ} (a b : Set.Icc l r) : Path a b where
  toFun := Icc.convexComb a b
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

/-- Pointwise affine interpolation is an endpoint-fixed homotopy in the same
closed interval. No ambient simply-connectedness assumption is used. -/
def realIntervalHomotopy {l r : ℝ} {a b : Set.Icc l r} (p q : Path a b) :
    p.Homotopy q where
  toFun z := Icc.convexComb (p z.2) (q z.2) z.1
  continuous_toFun := by fun_prop
  map_zero_left t := by simp
  map_one_left t := by simp
  prop' t s hs := by rcases hs with rfl | rfl <;> simp

/-- A real subinterval between unit-interval endpoints embeds into that actual
unit interval without choosing any affine reparametrization. -/
def intervalToUnit (l r : unitInterval) : C(Set.Icc (l : ℝ) (r : ℝ), unitInterval) where
  toFun a := ⟨a.val, l.property.1.trans a.property.1, a.property.2.trans r.property.2⟩
  continuous_toFun := by fun_prop

variable {X : Type u} [TopologicalSpace X] {ι : Type v} {U : ι → Set X}

/-- Four affine subpaths whose parameter vertices lie in one closed interval
admit an actual chart-contained boundary homotopy when the entire interval
image is in the chart. The conclusion is not inferred from boundary containment alone. -/
def subpathSquareFilling {x y : X} (p : Path x y) (i : ι)
    (l r : unitInterval) (a b c e : Set.Icc (l : ℝ) (r : ℝ))
    (hp : ∀ t : Set.Icc (l : ℝ) (r : ℝ), p (intervalToUnit l r t) ∈ U i) :
    SquareFilling (U := U)
      (p.subpath (intervalToUnit l r a) (intervalToUnit l r b))
      (p.subpath (intervalToUnit l r a) (intervalToUnit l r c))
      (p.subpath (intervalToUnit l r b) (intervalToUnit l r e))
      (p.subpath (intervalToUnit l r c) (intervalToUnit l r e)) := by
  let f : C(Set.Icc (l : ℝ) (r : ℝ), X) := p.toContinuousMap.comp (intervalToUnit l r)
  have contained (v w : Set.Icc (l : ℝ) (r : ℝ)) :
      Set.range (p.subpath (intervalToUnit l r v) (intervalToUnit l r w)) ⊆ U i := by
    rintro _ ⟨t, rfl⟩
    exact hp (Icc.convexComb v w t)
  let H := realIntervalHomotopy ((realIntervalPath a b).trans (realIntervalPath b e))
    ((realIntervalPath a c).trans (realIntervalPath c e))
  refine {
    chart := i
    top := contained a b
    left := contained a c
    right := contained b e
    bottom := contained c e
    homotopy := {
      toFun := fun z => f (H z)
      continuous_toFun := f.continuous.comp H.continuous
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }
    contained := fun z => hp (H z) }
  · intro t
    refine (congrArg f (H.map_zero_left t)).trans ?_
    simp only [Path.coe_toContinuousMap, Path.trans_apply]
    split <;> rfl
  · intro t
    refine (congrArg f (H.map_one_left t)).trans ?_
    simp only [Path.coe_toContinuousMap, Path.trans_apply]
    split <;> rfl
  · intro t z hz
    rcases hz with rfl | rfl
    · change f (H (t, 0)) = _
      exact (congrArg f (H.source t)).trans (Path.source _).symm
    · change f (H (t, 1)) = _
      exact (congrArg f (H.target t)).trans (Path.target _).symm

end FundamentalGroupoid.OpenCover
