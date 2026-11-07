/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.Topology.HomotopyFiber.ContractibleSourcePath
public import Colib.Topology.Homotopy.HomotopyGroup.BasedHomotopyInverse
/-!
Implementation provenance:
`Quillen/Topology/HomotopyFiber/ContractibleSourcePathGroups.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# The original corrected loop and fiber maps are inverse on homotopy classes

These formulas retain the actual unit-removal path and the already specified
inverse-basepoint path. They permit cancellation of the explicit forward map
without claiming that the chosen contraction or inverse is natural.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
namespace Topology.HomotopyFiber
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable [ContractibleSpace X] (f : C(X, Y)) (x : X) (y : Y) (γ : Path (f x) y)

/-- The original inverse and its displayed basepoint path undo the corrected forward map. -/
theorem loopEquivOfContractibleSourcePath_inverse_pi (n : ℕ)
    (a : HomotopyGroup.Pi n (Path y y) (Path.refl y)) :
    pathTransport (loopEquivOfContractibleSourcePathInverseBasepointPath f x y γ) n
      (HomotopyGroup.map (loopEquivOfContractibleSourcePath f x y γ).invFun rfl
        (pathTransport (loopEquivOfContractibleSourcePathUnitPath f x y γ) n
          (HomotopyGroup.map (loopEquivOfContractibleSourcePath f x y γ).toFun rfl a))) = a :=
  pathTransport_homotopyEquiv_inverse (loopEquivOfContractibleSourcePath f x y γ)
    (Path.refl y) (pointWithPath f x y γ)
    (loopEquivOfContractibleSourcePathUnitPath f x y γ)
    (Classical.choice (loopEquivOfContractibleSourcePath f x y γ).left_inv) n a

/-- The displayed forward map likewise undoes the original corrected inverse. -/
theorem loopEquivOfContractibleSourcePath_forward_pi (n : ℕ)
    (b : HomotopyGroup.Pi n (HomotopyFiber f y) (pointWithPath f x y γ)) :
    pathTransport (loopEquivOfContractibleSourcePathUnitPath f x y γ) n
      (HomotopyGroup.map (loopEquivOfContractibleSourcePath f x y γ).toFun rfl
        (pathTransport (loopEquivOfContractibleSourcePathInverseBasepointPath f x y γ) n
          (HomotopyGroup.map (loopEquivOfContractibleSourcePath f x y γ).invFun rfl b))) = b :=
  pathTransport_homotopyEquiv_forward (loopEquivOfContractibleSourcePath f x y γ)
    (Path.refl y) (pointWithPath f x y γ)
    (loopEquivOfContractibleSourcePathUnitPath f x y γ)
    (Classical.choice (loopEquivOfContractibleSourcePath f x y γ).left_inv) n b
end Topology.HomotopyFiber
