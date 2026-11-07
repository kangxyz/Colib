/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.Basic
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.DegreeShift

/-!
Implementation provenance:
`Quillen/Topology/HomotopyFiber/Loop.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

The actual fiber of a based loop map is homeomorphic to loops in the original fiber, by transposing
independent path parameters.
-/
@[expose] public section


noncomputable section
open scoped Topology unitInterval
universe u v
namespace Topology.HomotopyFiber
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X, Y)) {x : X} {y : Y} (h : f x = y)

/-- Transposing the two actual path parameters identifies the fiber of the
based loop map with the based loops in the original path-space fiber. -/
def loopFiberHomeomorph :
    HomotopyFiber (basedLoopMap f h) (Path.refl y) ≃ₜ
      Path (basepoint f y x h) (basepoint f y x h) where
  toFun z :=
    { toFun t := ⟨(z.1.1 t, ⟨fun s ↦ z.1.2 s t, by fun_prop⟩),
        by exact congrArg (fun p : Path y y ↦ p t) z.2.1,
        by exact congrArg (fun p : Path y y ↦ p t) z.2.2⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        apply Continuous.prodMk
        · fun_prop
        · apply ContinuousMap.continuous_of_continuous_uncurry
          change Continuous (fun q : unitInterval × unitInterval ↦ z.1.2 q.2 q.1)
          fun_prop
      source' := by
        apply Subtype.ext
        apply Prod.ext z.1.1.source
        apply ContinuousMap.ext
        intro s
        exact (z.1.2 s).source
      target' := by
        apply Subtype.ext
        apply Prod.ext z.1.1.target
        apply ContinuousMap.ext
        intro s
        exact (z.1.2 s).target }
  invFun γ :=
    ⟨( { toFun t := (γ t).1.1
         continuous_toFun := by fun_prop
         source' := congrArg (fun z : HomotopyFiber f y ↦ z.1.1) γ.source
         target' := congrArg (fun z : HomotopyFiber f y ↦ z.1.1) γ.target },
       { toFun s :=
           { toFun t := (γ t).1.2 s
             continuous_toFun := by fun_prop
             source' := congrArg (fun z : HomotopyFiber f y ↦ z.1.2 s) γ.source
             target' := congrArg (fun z : HomotopyFiber f y ↦ z.1.2 s) γ.target }
         continuous_toFun := by
           apply Path.continuous_uncurry_iff.mp
           change Continuous (fun q : unitInterval × unitInterval ↦ (γ q.2).1.2 q.1)
           fun_prop }),
      by apply Path.ext; funext t; exact (γ t).2.1,
      by apply Path.ext; funext t; exact (γ t).2.2⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · apply Path.ext; rfl
    · apply ContinuousMap.ext; intro s; apply Path.ext; rfl
  right_inv γ := by
    apply Path.ext
    funext t
    apply Subtype.ext
    apply Prod.ext rfl
    apply ContinuousMap.ext
    intro s
    rfl
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · fun_prop
    · apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun q : (HomotopyFiber (basedLoopMap f h) (Path.refl y) × unitInterval) ×
        unitInterval ↦ q.1.1.1.2 q.2 q.1.2)
      fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · apply Path.continuous_uncurry_iff.mp
      change Continuous (fun q : Path (basepoint f y x h) (basepoint f y x h) × unitInterval ↦ (q.1
        q.2).1.1)
      fun_prop
    · apply ContinuousMap.continuous_of_continuous_uncurry
      apply Path.continuous_uncurry_iff.mp
      change Continuous (fun q : (Path (basepoint f y x h) (basepoint f y x h) × unitInterval) ×
        unitInterval ↦ (q.1.1 q.2).1.2 q.1.2)
      fun_prop

@[simp] theorem loopFiberHomeomorph_source
    (z : HomotopyFiber (basedLoopMap f h) (Path.refl y)) (t : unitInterval) :
    (loopFiberHomeomorph f h z t).1.1 = z.1.1 t := rfl

@[simp] theorem loopFiberHomeomorph_path
    (z : HomotopyFiber (basedLoopMap f h) (Path.refl y)) (t s : unitInterval) :
    (loopFiberHomeomorph f h z t).1.2 s = z.1.2 s t := rfl

@[simp] theorem loopFiberHomeomorph_basepoint :
    loopFiberHomeomorph f h
      (basepoint (basedLoopMap f h) (Path.refl y) (Path.refl x)
        (basedLoopMap_refl f h)) = Path.refl (basepoint f y x h) := by
  apply Path.ext
  rfl

end Topology.HomotopyFiber
