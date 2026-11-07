/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyFiber.LES
public import Colib.Topology.HomotopyFiber.Loop
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.TransposeSign
public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalence

/-!
# The original connecting map and the fiber-loop transpose

The actual loop inclusion for the based loop map, followed by the existing fiber-loop
homeomorphism, interchanges the two original coordinates. These formulas are the precise
normalization input for the scalar-cofiber boundary calculation. The object-component
translation and the original Laurent unit class must still be compared separately.
-/
/-! Implementation source: `Quillen/Topology/HomotopyFiber/ConnectingLoopTranspose.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, basepoints,
coefficients and signs are retained with native Colib dependencies. -/
@[expose] public section
noncomputable section
open scoped Topology unitInterval
universe u v
namespace Topology.HomotopyFiber
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X, Y)) {x : X} {y : Y} (h : f x = y)

/-- The literal original inclusion into the loop-map fiber, transposed into a loop in the fiber. -/
def loopConnectingMap :
    C(Path (Path.refl y) (Path.refl y),
      Path (basepoint f y x h) (basepoint f y x h)) :=
  (loopFiberHomeomorph f h).toHomotopyEquiv.toFun.comp
    (loopInclusion (basedLoopMap f h) (Path.refl y) (Path.refl x)
      (basedLoopMap_refl f h))

/-- The source coordinate remains the original fixed source point. -/
theorem loopConnectingMap_source (γ : Path (Path.refl y) (Path.refl y))
    (t : unitInterval) :
    (loopConnectingMap f h γ t).val.1 = x := rfl

/-- The original fiber path and loop coordinates are interchanged literally. -/
theorem loopConnectingMap_path (γ : Path (Path.refl y) (Path.refl y))
    (t s : unitInterval) :
    (loopConnectingMap f h γ t).val.2 s = γ s t := rfl

/-- The transposed original inclusion retains its original constant-loop basepoint. -/
theorem loopConnectingMap_refl :
    loopConnectingMap f h (Path.refl (Path.refl y)) =
      Path.refl (basepoint f y x h) := by
  apply Path.ext
  rfl

/-- A literal double-loop transpose identifies this map with the loop of the original inclusion. -/
theorem loopConnectingMap_eq
    (τ : C(Path (Path.refl y) (Path.refl y), Path (Path.refl y) (Path.refl y)))
    (hτ : ∀ γ s t, τ γ s t = γ t s) :
    loopConnectingMap f h =
      (basedLoopMap (loopInclusion f y x h) (loopInclusion_refl f y x h)).comp τ := by
  apply ContinuousMap.ext
  intro γ
  apply Path.ext
  funext t
  apply Subtype.ext
  change (x, _) = (x, _)
  refine Prod.ext ?_ ?_
  · rfl
  · apply ContinuousMap.ext
    intro s
    exact (hτ γ t s).symm

/-- The original connecting homomorphism keeps the literal double-loop transpose before uncurrying.
-/
theorem connectingHom_loopConnectingMap
    (τ : C(Path (Path.refl y) (Path.refl y), Path (Path.refl y) (Path.refl y)))
    (hτ : τ (Path.refl (Path.refl y)) = Path.refl (Path.refl y))
    (hcoord : ∀ γ s t, τ γ s t = γ t s)
    (a : HomotopyGroup.Pi 0 (Path (Path.refl y) (Path.refl y))
      (Path.refl (Path.refl y))) :
    (loopShiftEquiv (x := basepoint f y x h) 0).symm
        (HomotopyGroup.map (loopConnectingMap f h) (loopConnectingMap_refl f h) a) =
      connectingHom f y x h 0
        ((loopShiftEquiv (x := y) 1).symm
          ((loopShiftEquiv (x := Path.refl y) 0).symm (HomotopyGroup.map τ hτ a))) := by
  let i := loopInclusion f y x h
  let hi := loopInclusion_refl f y x h
  have hm := congrFun (homotopyGroupMap_congr
    (loopConnectingMap_eq f h τ hcoord) (loopConnectingMap_refl f h)
    ((congrArg (basedLoopMap i hi) hτ).trans (basedLoopMap_refl i hi))) a
  have hm' := HomotopyGroup.map_comp τ hτ (basedLoopMap i hi)
    (basedLoopMap_refl i hi) a
  apply (loopShiftEquiv (x := basepoint f y x h) 0).injective
  rw [Equiv.apply_symm_apply]
  change HomotopyGroup.map (loopConnectingMap f h) (loopConnectingMap_refl f h) a =
    loopShiftEquiv 0 (HomotopyGroup.map i hi
      (loopShiftEquiv 1 ((loopShiftEquiv 1).symm
        ((loopShiftEquiv 0).symm (HomotopyGroup.map τ hτ a)))))
  rw [Equiv.apply_symm_apply, loopShiftEquiv_natural, Equiv.apply_symm_apply]
  exact hm.trans hm'

/-- The already proved two-coordinate sign gives inversion of the twice-uncurried class. -/
theorem connectingHom_loopConnectingMap_sign
    (τ : C(Path (Path.refl y) (Path.refl y), Path (Path.refl y) (Path.refl y)))
    (hτ : τ (Path.refl (Path.refl y)) = Path.refl (Path.refl y))
    (hcoord : ∀ γ s t, τ γ s t = γ t s)
    (a : HomotopyGroup.Pi 0 (Path (Path.refl y) (Path.refl y))
      (Path.refl (Path.refl y))) :
    (loopShiftEquiv (x := basepoint f y x h) 0).symm
        (HomotopyGroup.map (loopConnectingMap f h) (loopConnectingMap_refl f h) a) =
      connectingHom f y x h 0
        (((loopShiftEquiv (x := y) 1).symm
          ((loopShiftEquiv (x := Path.refl y) 0).symm a))⁻¹) := by
  rw [connectingHom_loopConnectingMap f h τ hτ hcoord a,
    loopShiftEquiv_twice_coordinateSwap 0 τ hτ hcoord a]

end Topology.HomotopyFiber
