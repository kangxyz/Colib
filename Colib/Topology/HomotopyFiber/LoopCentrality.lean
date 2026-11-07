/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyFiber.LES
public import Colib.Topology.Homotopy.HomotopyGroup.Product
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# The original loop-space image is central in the actual fiber fundamental group

Right concatenation of the stored fiber path by a target loop is a continuous
action. Its two unit slices are based homotopic to the identity and the original
loop inclusion. The two factors of the actual product fundamental group commute,
so their images under this action commute. Consequently the original degree-two
connecting map, and the kernel of the original fiber projection, have central
image. No connectivity hypothesis on the source or target is needed.
-/

/-! Implementation source: `Quillen/Topology/HomotopyFiber/LoopCentrality.lean`
at c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual maps, endpoint paths,
universes and signs are retained, with native Colib dependencies. -/
@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open scoped Topology unitInterval

universe u v

namespace Topology.HomotopyFiber

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable (f : C(X, Y)) (y : Y) (x : X) (h : f x = y)

/-- Append the entire target loop to the original stored fiber path. -/
def rightLoopAction : C(HomotopyFiber f y × Path y y, HomotopyFiber f y) where
  toFun z := ⟨(z.1.val.1, ((toPath f y z.1).trans z.2).toContinuousMap),
    ((toPath f y z.1).trans z.2).source, ((toPath f y z.1).trans z.2).target⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · exact (projection f y).continuous.comp continuous_fst
    apply ContinuousMap.continuous_of_continuous_uncurry
    refine Path.trans_continuous_family
      (fun z : HomotopyFiber f y × Path y y ↦ toPath f y z.1) ?_
      (fun z : HomotopyFiber f y × Path y y ↦ z.2) ?_
    · change Continuous (fun z : (HomotopyFiber f y × Path y y) × unitInterval ↦
        z.1.1.val.2 z.2)
      fun_prop
    · fun_prop

/-- Both constant paths remain exactly constant under the action. -/
@[simp] theorem rightLoopAction_basepoint :
    rightLoopAction f y (basepoint f y x h, Path.refl y) = basepoint f y x h := by
  subst y
  apply Subtype.ext
  change (x, ((Path.refl (f x)).trans (Path.refl (f x))).toContinuousMap) = _
  rw [Path.refl_trans_refl]
  rfl

/-- Removing the appended constant path is jointly continuous on the actual fiber. -/
def rightLoopActionUnitHomotopy :
    ((rightLoopAction f y).comp
      ((ContinuousMap.id _).prodMk (ContinuousMap.const _ (Path.refl y)))).Homotopy
      (ContinuousMap.id (HomotopyFiber f y)) where
  toFun z := ⟨(z.2.val.1, (Path.delayReflRight z.1 (toPath f y z.2)).toContinuousMap),
    (Path.delayReflRight z.1 (toPath f y z.2)).source,
    (Path.delayReflRight z.1 (toPath f y z.2)).target⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · exact (projection f y).continuous.comp continuous_snd
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : (unitInterval × HomotopyFiber f y) × unitInterval ↦
      z.1.2.val.2 (unitInterval.qRight (z.2, z.1.1)))
    fun_prop
  map_zero_left z := by
    apply Subtype.ext
    change (z.val.1, (Path.delayReflRight 0 (toPath f y z)).toContinuousMap) = _
    rw [Path.delayReflRight_zero]
    rfl
  map_one_left z := by
    apply Subtype.ext
    change (z.val.1, (Path.delayReflRight 1 (toPath f y z)).toContinuousMap) = _
    rw [Path.delayReflRight_one]
    rfl

/-- The unit homotopy is stationary at the original constant-path fiber basepoint. -/
@[simp] theorem rightLoopActionUnitHomotopy_basepoint (t : unitInterval) :
    rightLoopActionUnitHomotopy f y (t, basepoint f y x h) = basepoint f y x h := by
  apply Subtype.ext
  rfl

/-- Removing the initial constant path recovers the specified original loop inclusion. -/
def rightLoopActionOrbitHomotopy :
    ((rightLoopAction f y).comp
      ((ContinuousMap.const _ (basepoint f y x h)).prodMk
        (ContinuousMap.id (Path y y)))).Homotopy (loopInclusion f y x h) where
  toFun z := loopInclusion f y x h (Path.delayReflLeft z.1 z.2)
  continuous_toFun :=
    (loopInclusion f y x h).continuous.comp Path.continuous_delayReflLeft
  map_zero_left γ := by
    change loopInclusion f y x h (Path.delayReflLeft 0 γ) = _
    rw [Path.delayReflLeft_zero]
    subst y
    rfl
  map_one_left γ := by
    change loopInclusion f y x h (Path.delayReflLeft 1 γ) = _
    rw [Path.delayReflLeft_one]

/-- The orbit homotopy fixes the constant loop at the original fiber basepoint. -/
@[simp] theorem rightLoopActionOrbitHomotopy_basepoint (t : unitInterval) :
    rightLoopActionOrbitHomotopy f y x h (t, Path.refl y) = basepoint f y x h := rfl

/-- Every original loop-inclusion class commutes with every fiber fundamental-group class. -/
theorem commute_piOne_loopInclusion
    (a : HomotopyGroup.Pi 1 (HomotopyFiber f y) (basepoint f y x h))
    (b : HomotopyGroup.Pi 1 (Path y y) (Path.refl y)) :
    Commute a (HomotopyGroup.piMap 0 (loopInclusion f y x h) (loopInclusion_refl f y x h) b) := by
  let z := basepoint f y x h
  let e := Path.refl y
  let i₁ : C(HomotopyFiber f y, HomotopyFiber f y × Path y y) :=
    (ContinuousMap.id _).prodMk (ContinuousMap.const _ e)
  let i₂ : C(Path y y, HomotopyFiber f y × Path y y) :=
    (ContinuousMap.const _ z).prodMk (ContinuousMap.id _)
  let p₁ : HomotopyGroup.Pi 1 (HomotopyFiber f y) z →*
      HomotopyGroup.Pi 1 (HomotopyFiber f y × Path y y) (z, e) := HomotopyGroup.piMap 0 i₁ rfl
  let p₂ : HomotopyGroup.Pi 1 (Path y y) e →*
      HomotopyGroup.Pi 1 (HomotopyFiber f y × Path y y) (z, e) := HomotopyGroup.piMap 0 i₂ rfl
  have h₁ : piProdMap 0 z e (p₁ a) = (a, 1) := by
    induction a using Quotient.inductionOn with
    | h p => rfl
  have h₂ : piProdMap 0 z e (p₂ b) = (1, b) := by
    induction b using Quotient.inductionOn with
    | h p => rfl
  have hc : Commute (p₁ a) (p₂ b) := by
    apply (piProdMap_bijective 0 z e).injective
    rw [map_mul, map_mul, h₁, h₂]
    simp
  let μ : HomotopyGroup.Pi 1 (HomotopyFiber f y × Path y y) (z, e) →*
      HomotopyGroup.Pi 1 (HomotopyFiber f y) z :=
    HomotopyGroup.piMap 0 (rightLoopAction f y) (rightLoopAction_basepoint f y x h)
  have hm₁ : μ.comp p₁ = MonoidHom.id _ := by
    rw [← HomotopyGroup.mapHom_comp]
    exact (HomotopyGroup.piMap_eq_of_based_homotopy 0
      (f := (rightLoopAction f y).comp i₁) (g := ContinuousMap.id _)
      (show ((rightLoopAction f y).comp i₁) z = z from rightLoopAction_basepoint f y x h) rfl
      (rightLoopActionUnitHomotopy f y)
      (rightLoopActionUnitHomotopy_basepoint f y x h)).trans HomotopyGroup.mapHom_id
  have hm₂ : μ.comp p₂ =
      HomotopyGroup.piMap 0 (loopInclusion f y x h) (loopInclusion_refl f y x h) := by
    rw [← HomotopyGroup.mapHom_comp]
    exact HomotopyGroup.piMap_eq_of_based_homotopy 0 (f := (rightLoopAction f y).comp i₂)
      (g := loopInclusion f y x h)
      (show ((rightLoopAction f y).comp i₂) e = z from rightLoopAction_basepoint f y x h)
      (loopInclusion_refl f y x h) (rightLoopActionOrbitHomotopy f y x h)
      (rightLoopActionOrbitHomotopy_basepoint f y x h)
  have he := congrArg μ hc.eq
  rw [map_mul, map_mul] at he
  change (μ.comp p₁) a * (μ.comp p₂) b = (μ.comp p₂) b * (μ.comp p₁) a at he
  rw [hm₁, hm₂] at he
  exact he

/-- Centrality refers to the image of the original loop inclusion on actual Pi one. -/
theorem range_piOne_loopInclusion_le_center :
    (HomotopyGroup.piMap 0 (loopInclusion f y x h) (loopInclusion_refl f y x h)).range ≤
      Subgroup.center (HomotopyGroup.Pi 1 (HomotopyFiber f y) (basepoint f y x h)) := by
  rintro _ ⟨b, rfl⟩
  exact Subgroup.mem_center_iff.mpr (fun a ↦ (commute_piOne_loopInclusion f y x h a b).eq)

/-- The original degree-two connecting map has central image, with its loop shift retained. -/
theorem range_connectingHom_zero_le_center :
    (connectingHom f y x h 0).range ≤
      Subgroup.center (HomotopyGroup.Pi 1 (HomotopyFiber f y) (basepoint f y x h)) := by
  rintro _ ⟨a, rfl⟩
  exact range_piOne_loopInclusion_le_center f y x h ⟨_, rfl⟩

/-- The kernel of the actual fiber projection on Pi one is central. -/
theorem ker_piOne_projection_le_center :
    (HomotopyGroup.piMap 0 (projection f y) (projection_basepoint f y x h)).ker ≤
      Subgroup.center (HomotopyGroup.Pi 1 (HomotopyFiber f y) (basepoint f y x h)) := by
  rw [← range_connectingHom_eq_ker_projection f y x h 0]
  exact range_connectingHom_zero_le_center f y x h

end Topology.HomotopyFiber
