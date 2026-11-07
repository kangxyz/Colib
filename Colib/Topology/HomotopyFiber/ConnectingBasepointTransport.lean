/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyFiber.LoopPrefixBasepointNaturality
public import Colib.Topology.HomotopyFiber.LoopCentrality

/-!
# Original connecting classes along an actual fiber path

The actual prefix-unit correction at a constant-path fiber point is exactly
the original loop inclusion. The supplied whole fiber path therefore transports
each original degree-two connecting class to the original connecting class at
its other endpoint. No connectedness or choice of a source path is assumed.
-/

/-! Implementation source: `Quillen/Topology/HomotopyFiber/ConnectingBasepointTransport.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, basepoints,
coefficients and signs are retained with native Colib dependencies. -/
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

/-- At the original constant-path point, prefix correction is the original loop inclusion. -/
theorem canonical_loopPrefix_corrected_piOne
    (a : HomotopyGroup.Pi 1 (Path y y) (Path.refl y)) :
    pathTransport (loopPrefixUnitPath f x y (toPath f y (basepoint f y x h))) 1
      (HomotopyGroup.map (loopPrefix f x y (toPath f y (basepoint f y x h))) rfl a) =
        HomotopyGroup.piMap 0 (loopInclusion f y x h) (loopInclusion_refl f y x h) a := by
  let H := rightLoopActionOrbitHomotopy f y x h
  have hp : H.evalAt (Path.refl y) =
      loopPrefixUnitPath f x y (toPath f y (basepoint f y x h)) := by
    ext t
    apply Subtype.ext
    rfl
  have ht := pathTransport_homotopyGroupMap_homotopy H (Path.refl y) 1 a
  rw [hp] at ht
  exact ht

/-- Every original connecting class follows the entire displayed path between fiber basepoints. -/
theorem pathTransport_connectingHom_zero {x₀ x₁ : X} (h₀ : f x₀ = y) (h₁ : f x₁ = y)
    (q : Path (basepoint f y x₀ h₀) (basepoint f y x₁ h₁))
    (a : HomotopyGroup.Pi 2 Y y) :
    pathTransport q 1 (connectingHom f y x₀ h₀ 0 a) = connectingHom f y x₁ h₁ 0 a := by
  have ht := loopPrefix_pathTransport_pi q 1 (loopShiftMulEquiv (x := y) 0 a)
  exact ((congrArg (pathTransport q 1)
    (canonical_loopPrefix_corrected_piOne f y x₀ h₀
      (loopShiftMulEquiv (x := y) 0 a)).symm).trans ht).trans
    (canonical_loopPrefix_corrected_piOne f y x₁ h₁ (loopShiftMulEquiv (x := y) 0 a))

end Topology.HomotopyFiber
