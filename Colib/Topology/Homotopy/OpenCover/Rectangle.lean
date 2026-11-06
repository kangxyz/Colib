/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Homotopy.OpenCover.Independence

/-!
# Rectangle

The actual vertical path of an ambient path homotopy at a fixed parameter.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Set CategoryTheory
universe u v
namespace FundamentalGroupoid.OpenCover

/-- The actual vertical path of an ambient path homotopy at a fixed parameter. -/
def homotopyColumn {X : Type u} [TopologicalSpace X] {x y : X}
    {p q : Path x y} (H : p.Homotopy q) (t : unitInterval) : Path (p t) (q t) where
  toFun s := H (s, t)
  continuous_toFun := H.continuous.comp (continuous_id.prodMk continuous_const)
  source' := H.map_zero_left t
  target' := H.map_one_left t

/-- Horizontal affine traversal of a real closed rectangle. -/
def rectangleHorizontal {l r a b : ℝ} (s : Set.Icc l r) (t z : Set.Icc a b) :
    Path (s, t) (s, z) where
  toFun u := (s, Icc.convexComb t z u)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

/-- Vertical affine traversal of a real closed rectangle. -/
def rectangleVertical {l r a b : ℝ} (t : Set.Icc a b) (s z : Set.Icc l r) :
    Path (s, t) (z, t) where
  toFun u := (Icc.convexComb s z u, t)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

/-- Endpoint-fixed interpolation of arbitrary actual paths in one rectangle. -/
def realRectangleHomotopy {l r a b : ℝ} {x y : Set.Icc l r × Set.Icc a b}
    (p q : Path x y) : p.Homotopy q where
  toFun z := (Icc.convexComb (p z.2).1 (q z.2).1 z.1,
    Icc.convexComb (p z.2).2 (q z.2).2 z.1)
  continuous_toFun := by fun_prop
  map_zero_left t := by simp
  map_one_left t := by simp
  prop' t s hs := by rcases hs with rfl | rfl <;> simp

variable {X : Type u} [TopologicalSpace X] {ι : Type v} {U : ι → Set X}

/-- Restricting an actual ambient path homotopy to a subordinate closed rectangle
produces a genuine chart-contained boundary filling. Every point of the entire
rectangle image is required to lie in the chart, not only its four edges. -/
def homotopyRectangleFilling {x y : X} {p q : Path x y} (H : p.Homotopy q)
    (l r a b : unitInterval) (hlr : l ≤ r) (hab : a ≤ b) (i : ι)
    (hi : H '' (Set.Icc l r ×ˢ Set.Icc a b) ⊆ U i) :
    SquareFilling (U := U)
      ((H.eval l).subpath a b) ((homotopyColumn H a).subpath l r)
      ((homotopyColumn H b).subpath l r) ((H.eval r).subpath a b) := by
  let sl : Set.Icc (l : ℝ) (r : ℝ) := ⟨l, le_rfl, hlr⟩
  let sr : Set.Icc (l : ℝ) (r : ℝ) := ⟨r, hlr, le_rfl⟩
  let ta : Set.Icc (a : ℝ) (b : ℝ) := ⟨a, le_rfl, hab⟩
  let tb : Set.Icc (a : ℝ) (b : ℝ) := ⟨b, hab, le_rfl⟩
  let f : C(Set.Icc (l : ℝ) (r : ℝ) × Set.Icc (a : ℝ) (b : ℝ), X) :=
    ⟨fun z => H (intervalToUnit l r z.1, intervalToUnit a b z.2), by fun_prop⟩
  have hf (z : Set.Icc (l : ℝ) (r : ℝ) × Set.Icc (a : ℝ) (b : ℝ)) : f z ∈ U i :=
    hi ⟨(intervalToUnit l r z.1, intervalToUnit a b z.2),
      ⟨⟨z.1.property.1, z.1.property.2⟩, ⟨z.2.property.1, z.2.property.2⟩⟩, rfl⟩
  let K := realRectangleHomotopy
    ((rectangleHorizontal sl ta tb).trans (rectangleVertical tb sl sr))
    ((rectangleVertical ta sl sr).trans (rectangleHorizontal sr ta tb))
  refine {
    chart := i
    top := ?_
    left := ?_
    right := ?_
    bottom := ?_
    homotopy := {
      toFun := fun z => f (K z)
      continuous_toFun := f.continuous.comp K.continuous
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }
    contained := fun z => hf (K z) }
  · rintro _ ⟨t, rfl⟩
    exact hf (sl, Icc.convexComb ta tb t)
  · rintro _ ⟨t, rfl⟩
    exact hf (Icc.convexComb sl sr t, ta)
  · rintro _ ⟨t, rfl⟩
    exact hf (Icc.convexComb sl sr t, tb)
  · rintro _ ⟨t, rfl⟩
    exact hf (sr, Icc.convexComb ta tb t)
  · intro t
    refine (congrArg f (K.map_zero_left t)).trans ?_
    dsimp only [Path.trans, ContinuousMap.coe_mk, Function.comp_apply]
    split <;> rfl
  · intro t
    refine (congrArg f (K.map_one_left t)).trans ?_
    dsimp only [Path.trans, ContinuousMap.coe_mk, Function.comp_apply]
    split <;> rfl
  · intro t z hz
    rcases hz with rfl | rfl
    · change f (K (t, 0)) = _
      exact (congrArg f (K.source t)).trans (Path.source _).symm
    · change f (K (t, 1)) = _
      exact (congrArg f (K.target t)).trans (Path.target _).symm

end FundamentalGroupoid.OpenCover
